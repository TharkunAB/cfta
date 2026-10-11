# Grouped recursive key discovery

`GroupedProbe.lean` implements the `recurGrouped` key-discovery loop. Each pass
rebuilds the family and takes the union with the previous key map. Duplicate
keys keep the smaller discovered minimum. A missing key differs from a key
whose minimum is `NoFiniteMember`.

`step_decreases` derives a lexicographic decrease from those operations.
`converge` therefore terminates for every total builder over a finite key
domain. `converge_fixed` proves actual map stability. `converge_refines` proves
that no discovered key or finite minimum bound is lost. The proof permits any
finite discovered size and requires no numeric upper bound.

`GroupedMinimum.lean` supplies a concrete source expression builder with finite
sources, keyed occurrences, pay, choices, and products. Its finite derivation
semantics is independent of the discovery algorithm. `discover_minimum` proves
that each reported number is the least attained size at that key.
`liveKeys_exact` proves that the final finite-minimum filter keeps every key
with a finite derivation and no others.

The finite key domain is a source precondition. `recurGrouped` documents that
the key set must be finite. `successor_never_stable` proves a concrete total
builder that adds a new natural key on every pass. This is the documented
termination boundary, not a newly reported implementation defect.

These files model the minimum and key portion of the caller. The concrete
builder covers the specified expression algebra. They do not prove the
translation of arbitrary Haskell key functions, grouping, joins, nested
recursion, or user inspection into that algebra. The later occurrence-flag,
mass, sampler, term, support, and inspection knots remain separate fields.
The model records those boundaries explicitly; loop stability alone is not
a proof of all grouped-generator behavior.
