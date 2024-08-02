#![feature(test)]
extern crate test;

use std::{mem, ops};
use std::{error, fmt};

/// An enumeration of buffer creation errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// No choices were provided to the Unstructured::choose call
    EmptyChoose,
    /// There was not enough underlying data to fulfill some request for raw
    /// bytes.
    NotEnoughData,
    /// The input bytes were not of the right format
    IncorrectFormat,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::EmptyChoose => write!(
                f,
                "`arbitrary::Unstructured::choose` must be given a non-empty set of choices"
            ),
            Error::NotEnoughData => write!(
                f,
                "There is not enough underlying raw data to construct an `Arbitrary` instance"
            ),
            Error::IncorrectFormat => write!(
                f,
                "The raw data is not of the correct format to construct this type"
            ),
        }
    }
}

impl error::Error for Error {}

/// A `Result` with the error type fixed as `arbitrary::Error`.
///
/// Either an `Ok(T)` or `Err(arbitrary::Error)`.
pub type Result<T, E = Error> = std::result::Result<T, E>;


pub trait Int<const Bytes: usize>:
    Copy
    + std::fmt::Debug
    + PartialOrd
    + Ord
    + ops::Sub<Self, Output = Self>
    + ops::Rem<Self, Output = Self>
    + ops::Shr<Self, Output = Self>
    + ops::Shl<usize, Output = Self>
    + ops::BitOr<Self, Output = Self>
{
    #[doc(hidden)]
    type Unsigned: Int<Bytes>;

    #[doc(hidden)]
    const ZERO: Self;

    #[doc(hidden)]
    const ONE: Self;

    #[doc(hidden)]
    const MAX: Self;

    #[doc(hidden)]
    fn from_u8(b: u8) -> Self;

    #[doc(hidden)]
    fn from_usize(u: usize) -> Self;

    #[doc(hidden)]
    fn checked_add(self, rhs: Self) -> Option<Self>;

    #[doc(hidden)]
    fn wrapping_add(self, rhs: Self) -> Self;

    #[doc(hidden)]
    fn wrapping_sub(self, rhs: Self) -> Self;

    #[doc(hidden)]
    fn to_unsigned(self) -> Self::Unsigned;

    #[doc(hidden)]
    fn from_unsigned(unsigned: Self::Unsigned) -> Self;

    #[doc(hidden)]
    fn from_be_bytes(bytes: [u8; Bytes]) -> Self;

    #[doc(hidden)]
    fn to_be_bytes(self) -> [u8; Bytes];

    #[doc(hidden)]
    fn ilog2(self) -> u32;
}

macro_rules! impl_int {
    ( $( $ty:ty : $unsigned_ty: ty : $bytes:expr ; )* ) => {
        $(
            impl Int<$bytes> for $ty {
                type Unsigned = $unsigned_ty;

                const ZERO: Self = 0;

                const ONE: Self = 1;

                const MAX: Self = Self::MAX;

                fn from_u8(b: u8) -> Self {
                    b as Self
                }

                fn from_usize(u: usize) -> Self {
                    u as Self
                }

                fn checked_add(self, rhs: Self) -> Option<Self> {
                    <$ty>::checked_add(self, rhs)
                }

                fn wrapping_add(self, rhs: Self) -> Self {
                    <$ty>::wrapping_add(self, rhs)
                }

                fn wrapping_sub(self, rhs: Self) -> Self {
                    <$ty>::wrapping_sub(self, rhs)
                }

                fn to_unsigned(self) -> Self::Unsigned {
                    self as $unsigned_ty
                }

                fn from_unsigned(unsigned: $unsigned_ty) -> Self {
                    unsigned as Self
                }

                fn from_be_bytes(bytes: [u8; $bytes]) -> Self {
                    <$ty>::from_be_bytes(bytes)
                }

                fn to_be_bytes(self) -> [u8; $bytes] {
                    <$ty>::to_be_bytes(self)
                }

                fn ilog2(self) -> u32 {
                    <$ty>::ilog2(self)
                }
            }
        )*
    }
}

impl_int! {
    u8: u8 : 1;
    u16: u16 : 2;
    u32: u32 : 4;
    u64: u64 : 8;
    u128: u128 : 16;
    usize: usize : 8;
    i8: u8 : 1;
    i16: u16 : 2;
    i32: u32 : 4;
    i64: u64 : 8;
    i128: u128 : 16;
    isize: usize : 8;
}

fn int_in_range_impl_native<T, const Bytes: usize>(
    range: ops::RangeInclusive<T>,
    bytes: impl Iterator<Item = u8> + ExactSizeIterator,
) -> Result<(T, usize)>
where
    T: Int<Bytes>,
{
    let start = *range.start();
    let end = *range.end();
    assert!(
        start <= end,
        "`arbitrary::Unstructured::int_in_range` requires a non-empty range"
    );
    // When there is only one possible choice, don't waste any entropy from
    // the underlying data.
    if start == end {
        return Ok((start, 0));
    }

    // From here on out we work with the unsigned representation. All of the
    // operations performed below work out just as well whether or not `T`
    // is a signed or unsigned integer.
    let start = start.to_unsigned();
    let end = end.to_unsigned();

    let delta = end.wrapping_sub(start);
    debug_assert_ne!(delta, T::Unsigned::ZERO);

    // Compute an arbitrary integer offset from the start of the range. We
    // do this by consuming `size_of(T)` bytes from the input to create an
    // arbitrary integer and then clamping that int into our range bounds
    // with a modulo operation.

    // The min amount of bytes we need to represent delta
    let bytes_consumed = std::cmp::min(
        Bytes,
        (delta.ilog2() + 1).div_ceil(8) as usize
    );

    let mut byte_slice = [0u8; Bytes];

    let taken_bytes = bytes.take(bytes_consumed).collect::<Vec<_>>();
    // SAFETY: consumed_slice.len() is always <= Bytes
    byte_slice[0..taken_bytes.len()].copy_from_slice(&taken_bytes);
    let arbitrary_int = T::Unsigned::from_be_bytes(byte_slice);

    let offset = if delta == T::Unsigned::MAX {
        arbitrary_int
    } else {
        arbitrary_int % (delta.checked_add(T::Unsigned::ONE).unwrap())
    };

    // Finally, we add `start` to our offset from `start` to get the result
    // actual value within the range.
    let result = start.wrapping_add(offset);

    // And convert back to our maybe-signed representation.
    let result = T::from_unsigned(result);
    debug_assert!(*range.start() <= result);
    debug_assert!(result <= *range.end());

    Ok((result, bytes_consumed))
}

fn int_in_range_impl<T, const Bytes: usize>(
    range: ops::RangeInclusive<T>,
    mut bytes: impl Iterator<Item = u8>,
) -> Result<(T, usize)>
where
    T: Int<Bytes>,
{
    let start = *range.start();
    let end = *range.end();
    assert!(
        start <= end,
        "`arbitrary::Unstructured::int_in_range` requires a non-empty range"
    );

    // When there is only one possible choice, don't waste any entropy from
    // the underlying data.
    if start == end {
        return Ok((start, 0));
    }

    // From here on out we work with the unsigned representation. All of the
    // operations performed below work out just as well whether or not `T`
    // is a signed or unsigned integer.
    let start = start.to_unsigned();
    let end = end.to_unsigned();

    let delta = end.wrapping_sub(start);
    debug_assert_ne!(delta, T::Unsigned::ZERO);

    // Compute an arbitrary integer offset from the start of the range. We
    // do this by consuming `size_of(T)` bytes from the input to create an
    // arbitrary integer and then clamping that int into our range bounds
    // with a modulo operation.
    let mut arbitrary_int = T::Unsigned::ZERO;
    let mut bytes_consumed: usize = 0;

    while (bytes_consumed < mem::size_of::<T>())
        && (delta >> T::Unsigned::from_usize(bytes_consumed * 8)) > T::Unsigned::ZERO
    {
        let byte = match bytes.next() {
            None => break,
            Some(b) => b,
        };
        bytes_consumed += 1;

        // Combine this byte into our arbitrary integer, but avoid
        // overflowing the shift for `u8` and `i8`.
        arbitrary_int = if mem::size_of::<T>() == 1 {
            T::Unsigned::from_u8(byte)
        } else {
            (arbitrary_int << 8) | T::Unsigned::from_u8(byte)
        };
    }

    let offset = if delta == T::Unsigned::MAX {
        arbitrary_int
    } else {
        arbitrary_int % (delta.checked_add(T::Unsigned::ONE).unwrap())
    };

    // Finally, we add `start` to our offset from `start` to get the result
    // actual value within the range.
    let result = start.wrapping_add(offset);

    // And convert back to our maybe-signed representation.
    let result = T::from_unsigned(result);
    debug_assert!(*range.start() <= result);
    debug_assert!(result <= *range.end());

    Ok((result, bytes_consumed))
}

fn main() {
    let bytes = [8u8, 255u8];
    println!("{:?}", u16::from_be_bytes(bytes));
    println!("{:?}", int_in_range_impl(0..=u16::MAX, bytes.iter().cloned()));
}

#[cfg(kani)]
#[kani::proof]
fn check_estimate_size_u8() {
    let bytes: [u8; 1] = kani::any();
    let be_bytes = u8::from_be_bytes(bytes);
    let impl_bytes = int_in_range_impl(0..=u8::MAX, bytes.iter().cloned());
    assert_eq!(be_bytes, impl_bytes.unwrap().0)
}

#[cfg(kani)]
#[kani::proof]
fn check_estimate_size_u16() {
    let bytes: [u8; 2] = kani::any();
    let be_bytes = u16::from_be_bytes(bytes);
    let impl_bytes = int_in_range_impl(0..=u16::MAX, bytes.iter().cloned());
    assert_eq!(be_bytes, impl_bytes.unwrap().0)
}

#[cfg(kani)]
#[kani::proof]
fn check_estimate_size_u32() {
    let bytes: [u8; 4] = kani::any();
    let be_bytes = u32::from_be_bytes(bytes);
    let impl_bytes = int_in_range_impl(0..=u32::MAX, bytes.iter().cloned());
    assert_eq!(be_bytes, impl_bytes.unwrap().0)
}

#[cfg(kani)]
#[kani::proof]
fn check_estimate_size_u64() {
    let bytes: [u8; 8] = kani::any();
    let be_bytes = u64::from_be_bytes(bytes);
    let impl_bytes = int_in_range_impl(0..=u64::MAX, bytes.iter().cloned());
    assert_eq!(be_bytes, impl_bytes.unwrap().0)
}

#[cfg(kani)]
#[kani::proof]
fn check_estimate_size_u128() {
    let bytes: [u8; 16] = kani::any();
    let be_bytes = u128::from_be_bytes(bytes);
    let impl_bytes = int_in_range_impl(0..=u128::MAX, bytes.iter().cloned());
    assert_eq!(be_bytes, impl_bytes.unwrap().0)
}

#[cfg(test)]
mod tests {
    use test::{Bencher, black_box};

    use crate::{int_in_range_impl, int_in_range_impl_native};

    #[bench]
    fn bench_be_bytes(b: &mut Bencher) {
        let bytes: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        b.iter(|| {
            black_box(u128::from_be_bytes(bytes));
        })
    }

    #[bench]
    fn bench_range_impl_set_range(b: &mut Bencher) {
        let bytes: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        b.iter(|| {
            black_box(int_in_range_impl(5874154..=498529536, bytes.iter().cloned()));
        })
    }

    #[bench]
    fn bench_range_impl_all(b: &mut Bencher) {
        let bytes: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        b.iter(|| {
            black_box(int_in_range_impl(0..=u128::MAX, bytes.iter().cloned()));
        })
    }

    #[bench]
    fn bench_range_impl_set_range_native(b: &mut Bencher) {
        let bytes: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        b.iter(|| {
            black_box(int_in_range_impl_native(5874154..=498529536, bytes.iter().cloned()));
        })
    }

    #[bench]
    fn bench_range_impl_all_native(b: &mut Bencher) {
        let bytes: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        b.iter(|| {
            black_box(int_in_range_impl_native(0..=u128::MAX, bytes.iter().cloned()));
        })
    }
}