# Typed grouped minimum witnesses

`KeyedMinimumWitness.lean` connects the metadata-only grouped discovery
algorithm to actual typed values. `evaluate_attains` constructs a typed value
at every successful expression minimum from already witnessed occurrences.
`step_sound` and `converge_sound` preserve those witnesses through the concrete
key-union loop.

`minima_exact` proves that the stored minimum is the least attained typed
member size. `liveKeys_exact` proves that the final productive-key filter
retains exactly the keys with finite typed derivations. This removes the gap
between `GroupedMinimum`'s size grammar and `KeyedSource`'s value grammar.
No source productivity or minimum-correctness postcondition is assumed.

The result uses the same finite declared key domain and typed body algebra as
the grouped source files. It does not infer a finite reachable key domain for
an arbitrary Haskell key function. It also does not prove the final source
mapping that omits unavailable map entries or the enclosing-token flag knot.
