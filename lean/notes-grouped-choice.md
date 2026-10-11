# Public grouped choice

`GroupedChoice.lean` implements the branch selection in
`Gen.Internal.Grouped.frequencies` and `uniformlyGrouped`.

The worker checks nonpositive weights first. It then preserves the first
nonempty construction error. It removes empty alternatives. A recursive choice
requires equal weights among the remaining alternatives. Otherwise it returns
`WeightedRecursiveAlternatives`. Finite choices keep their declared branch
shares. `live_member` proves that successful alternatives retain their order
and multiplicity. `live_positive` and `normalized_live_positive` derive positive
coefficients from actual public validation.

`compileFiniteByKey` multiplies each bucket mass by its branch coefficient and
collects the matching key. `compileFiniteByKey_valid` proves the resulting
count/mass/decoder/sampler record invariant. `compileFiniteByKey_values` proves
that every source member at that key is retained, including duplicate values
and repeated alternatives. `compileRecursive_valid` connects equal-weight
recursive dispatch to the mass-weighted recursive class merge.

`uniformly` reads finite family cardinalities as its branch weights. When any
input has the recursive constructor, it takes the oneof-style path before
discarding empty alternatives. The checked examples distinguish those two
paths. In particular, an empty recursive input can change finite branch shares
from cardinality weighting to equal alternative weighting. This follows the
documented source branch policy; it is not reported as a new defect.

The payload interface supplies successful finite cardinality and the relevant
key records. The finite record theorems compute and validate those fields in
their own source algebra. This module does not derive every `staticView`,
`recursiveGroups`, key sorting, or user key-function adapter. It records
construction failures as opaque preserved causes. Random backend behavior and
external effects remain separate from the exact distribution semantics.
