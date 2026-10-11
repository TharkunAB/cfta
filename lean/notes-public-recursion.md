# Public recursive dispatch

`PublicRecursion.lean` joins the occurrence metadata and recursive record
models. `shape_minimum`, `size_guard_exact`, `term_guard_exact`, and `used_exact`
show that the typed source body computes the fields read by the actual source
probe. A finite source is erased to its attained minimum for this metadata
projection. The projection preserves zero-size tests and all occurrence flags.
It does not claim to preserve the full list of finite source sizes.

`close` returns an ordinary finite source exactly when the recursive body does
not use its occurrence. It preserves member order and source probability.
`compile` follows the public branch order: return an unused finite body; reject
unguarded recursion; reject an empty recursive language; construct a live knot.

The result theorems establish the following:

- `compile_finite_class` and `compile_finite_record` connect the returned finite
  source to independent derivations and the finite sampler record.
- `compile_unguarded` identifies rejection from the actual occurrence flags.
- `compile_empty` equates the empty error with absence of finite derivations,
  after the source's earlier branch checks.
- `compile_recursive_exact` derives productivity, exact class members, coherent
  rank replay, positive rank coverage, and the class probability recurrence.

The examples check positive-sibling guarding, pay-only rejection, and guarded
recursion without a base. The general theorems establish their contracts.

The input is the validated typed source algebra. Underlying construction errors
and opaque generators remain the separate `PublicResult` and `RecursionProbe`
dispatch cases. The module does not verify Haskell function inspection, nested
or grouped knot translation, token allocation, GHC lazy evaluation, term-view
callbacks, or support construction. It also does not identify equal output
values with equal source members. Those boundaries are stated separately from
the proved source record and public dispatch behavior.
