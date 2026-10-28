# Opaque and terminal child resource padding

This is a source review and proof recipe. This reviewer did not run Lean. The operation-level child theorems cited below are already checked repository dependencies. No `ProperState` premise is needed.

Use `ChildCompletion.complete_with_fragments_cache_bounds` in `SourcePruningEnumerationChildBoundedResources`. It has the exact original general child resource admission. It calls the original resource producer once. It retains the actual raw return, full caller/Post/Memos, roots/storage/realization/counts/flags, original fragment/protection/reference/history fields, final Fits and final guard Heap. It appends bounds for the same actual cache:

```
after.core.counter ≤ before.core.counter + 1
suspendedBound after.core ≤ suspendedBound before.core + bucket.length
```

This theorem handles ordinary, terminal, opaque, Empty, and rejected child routes. It does not assume a successful singleton. Its actual observation is at the producer's own sufficient bounds. `ChildDispatch.observed_cache_bounds` supplies the scalar result from that observation and the original Safe alignment.

The native endpoint profile is `advance seed (bucket.length + 1)`. It does not need to equal the planned `afterHead seed inherited`. Numeric and alphabet padding suffice.

Given original `fits : Fits seed.2 caller.checked`, derive positivity without a new premise:

```lean
have positive : 1 ≤ SourceCurrentConstrainedCapTargetForecast.scalar seed.2 :=
  Nat.le_trans fits.stored.positive
    (SourceCurrentConstrainedCapTargetForecast.scalar_mass seed.2)
```

`Stored.positive` is the existing field `1 ≤ seed.2.mass`. For `bucket.length ≤ inherited`, multiply `positive` by `inherited + guardWidth seed.1 + 1`. This gives:

```
bucket.length + 1 ≤ edgeCount seed inherited
```

Apply `HeadReserved.edge` or `.1.prefix` at this exact cost. Apply the existing `RecursiveReservation.head_padding seed inherited (bucket.length + 1) actualCostLe`. Its first component is the required `Le` to `afterHead`. Its second component is the required alphabet subset. Use `returnedFits.mono padding.1`. Transport the returned Heap as follows:

```lean
intro key edge resident
exact padding.2 (returnedKnown key edge resident)
```

This does not use generic heap extension to justify new annotations. The old child resource producer has already established the annotations at its actual reached heap. The subset only enlarges the planned alphabet.

For the same actual child cache, combine its mass bound with `suspendedBound before.core ≤ capturedMass` and `bucket.length ≤ inherited`. Multiply `positive` by `inherited + guardWidth seed.1`. This yields:

```
suspendedBound after.core ≤
  capturedMass + scalar seed.2 * (inherited + guardWidth seed.1)
```

The right side is exactly `RecursiveReservation.massCeil seed capturedMass inherited`. It counts the captured enumeration bucket mass. It is distinct from the normalized native AST mass.

A smaller-depth callback can therefore start at the original planned `afterHead` with the original planned `massCeil`. `PreparedReservation.afterHead_le_step` pads that callback's actual endpoint into the paired step. It uses the new prepared forecast at the smaller depth. No old ordinary fallback or old positive-depth completion theorem can replace the new worker's callback theorem.

The child packet's `raw=[]` case must keep the actual caller/cache effects. No callback is inferred there. A singleton case supplies Safe and fragment properties from the same returned shape; the owner must use those fields to form its actual callback admission. Post.query alone cannot replace full Memos.
