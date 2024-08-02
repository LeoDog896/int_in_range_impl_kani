# int_in_range_impl_kani

kani proofs for how a full range passed to `int_in_range_impl` is equal to `to_be_bytes`,
and accompanying benchmarks for the new impl. it isn't much faster, but it relies on standard definitions.

```
test tests::bench_be_bytes                    ... bench:           0.23 ns/iter (+/- 0.13)
test tests::bench_range_impl_all              ... bench:           9.99 ns/iter (+/- 2.55)
test tests::bench_range_impl_all_native       ... bench:           9.21 ns/iter (+/- 2.32)
test tests::bench_range_impl_set_range        ... bench:           0.42 ns/iter (+/- 0.06)
test tests::bench_range_impl_set_range_native ... bench:           0.39 ns/iter (+/- 0.12)
```
