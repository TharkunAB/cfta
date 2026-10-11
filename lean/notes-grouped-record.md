# Grouped class records

`GroupedRecord.lean` models the parallel mass and member fields of
`KeyedRecursive`. `Valid` requires a coherent live count/decoder/sampler record,
nonnegative key mass, and positive mass exactly when the class has members.
This keeps rank cardinality independent of probability.

`merge_valid` and `merge_probability` cover `mergeRecursiveGroups` and
`choiceMassSampleIndex`. Structural counts determine offsets. Retained masses
choose alternatives. Empty alternatives have no mass and no ranks.
`productClasses_valid`, `productClasses_values`, and
`productClasses_probability` cover every size split of a grouped product.
The split mass is the product of the component masses. Conditional member
probabilities remain the independent product of the component distributions.
`pay_valid` shifts all fields together. `bounded_valid` composes class records
through the actual count-weighted bounded sampler.

`counts` and `masses` implement the recursive public inspection formulas.
`counts_mass_filter` proves that they retain the same live key entries.
Ordinary finite classes use computed member counts. `retained` permits a
positive mass supplied by an atomic bucket or an earlier grouped operation.
Its precondition is mass positivity, not a desired sampler postcondition.

The module does not assert that arbitrary selected keys' masses sum to their
member counts. It proves the mass and conditional sampler relation used by
the source. Whole-family normalization, finite grouped public weight error
dispatch, and recursive body translation are separate caller obligations.
