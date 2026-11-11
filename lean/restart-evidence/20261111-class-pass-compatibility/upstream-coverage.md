# Scope of the integrated weighted APIs

Main `2abbfe8ea91aff49122c03e8c96ffa539053b7e1` adds weighted completion
training, parent features, mixtures, conditional probabilities, top-k queries,
and compiled sampler alternatives. The merge changes 27 paths. The validation
report records their exact hashes. All 523 generator examples and both example
checks pass. Fourmolu and cabal-gild also pass.

The existing Lean results do not establish implementation correspondence for
these new paths. Preserve these obligations when stating system coverage:

- `Ranked/Internal/Sampler.hs` and `Gen/Internal/Table.hs` now compose and cache
  sampling alternatives. Existing abstract sampler algebra does not identify
  this implementation. Probability claims also need the backend draw laws.
- Prefix weights and mixture shares use `Rational`. Training rationalizes
  finite exponential weights with tolerance `1e-9`. Log-probability queries use
  `Double`. No theorem identifies these representations as one exact measure
  or supplies a global error bound.
- `Prefix/Parents.hs`, `Train.hs`, `Model.hs`, and `Mixture.hs` need proofs for
  feature labeling, conditioning, posterior shares, and top-k results. The
  mixture threshold search can enumerate all completions. Its exact rational
  comparisons do not supply a termination or machine-bound theorem.
- A finite fitting report does not prove convergence or an optimum. Legacy
  fitting and mixture training also need numerical failure propagation. The
  separate training-oracle packet reproduces a numerical defect on one finite
  two-node term. It does not observe an empty mixture.

There is also an older size-dispatch coverage gap. `Sized.hs:155-176` routes
ambiguous unconstrained inputs through `deterministicCountingRows` and suitable
direct-child equality inputs through `intersectionCountingRows`. These routes
predate this merge. `Sized.hs` is not among the 27 changed paths. The current
`SourceSizedFiniteKeysDispatchApi.nativeSized` theorem models a narrower
dispatch and does not identify the whole current Haskell dispatcher.

Attach the language, duplicate, order, cutoff, and fallback contracts for those
routes before claiming coverage of both actual signed API instances. Negative
starting ranks also differ between enumeration and selection. Preserve their
actual behavior. These obligations remain part of the full library objective.
