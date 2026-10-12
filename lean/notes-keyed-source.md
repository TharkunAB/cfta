# Mutually recursive keyed records

`KeyedSource.lean` constructs typed class records for a whole recursive key
family. Leaves are closed finite sources or finite sources with a retained
positive key mass. The other constructors are keyed occurrence, map, pay,
same-key choice, and application. Each size reads only smaller sizes of any key.

`family_valid` derives each key's count, mass, decoder, and sampler invariant.
`family_values` and `family_count` preserve member order and multiplicity.
`family_exact` compares the compiled records with independent finite
derivations. It requires the size guard to accept each declared body. The proof
derives the key minima from `GroupedMinimum`; it does not assume a correct
minimum table. Cross-key product guards use the proved positive sibling cost.

`KeyedProbability.lean` supplies separate mass and probability recurrences.
`family_mass` proves that stored masses add across alternatives and convolve
across all product sizes. `family_probability` proves mass-weighted selection
and retained source distributions inside each key. `bounded_probability`
composes the exact conditional distributions with count-weighted size choice.
No independent sampler or count postcondition is assumed for recursive keys.

The finite source leaves already establish their record invariants. A retained
mass is an explicit positive input from a bucket or preceding grouped operation.
These modules do not yet derive that input for every finite grouping adapter.
The typed body is also not an extraction of arbitrary Haskell key functions or
nested recursive builders. `GroupedChoice` and `GroupedFlags` now prove
public branch validation, unavailable-key omission, enclosing occurrence flags,
and the finite-versus-recursive weight policy in their source ports. Concrete
heterogeneous record wiring remains a caller obligation. The theorem's guard
premise is explicit.

Members retain their structural ranks even when output values repeat. A distinct
term bijection still requires the separate source term-uniqueness invariant.
