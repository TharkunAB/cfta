# Native resource forecast review

Reviewed on 2026-10-17 at 08:08 CEST. The source is frozen at
`401fa57e9d964cd601fa2b0b0a1d79cdb37fbd9d37842da236d79b4acf6c6a1e`.

The new module contains only natural-number data and propositions. It imports
existing computed-query and mass monotonicity modules. Those modules have
physical dependencies, but this module introduces no physical state premise.

`Profile` records node, edge, domain, and stored payload mass bounds (lines
18–31). `step` uses the complete computed instruction bound from the node,
edge, and mass components. It charges both constructor counters by the
causal credit schedule, domains by the instruction count, and mass by the
causal mass schedule (lines 44–48). It does not charge only a successful
callback or a selected branch. The mass component is a payload bound. It is
not a memory byte count or a runtime estimate.

`step_ge` and `step_mono` use the existing schedule growth and monotonicity
laws. `advance` applies one step before the remaining forecast. Its addition
law preserves that order (lines 66–102). The profile order compares every
component. No converse comparison is used.

`Room` uses exactly the existing query-entry inequalities, including strict
node and domain inequalities and the non-strict edge inequality (lines
105–115). `Room.mono` is downward: a larger reserved profile can admit a
smaller actual profile. Its exponent comparison uses node monotonicity twice
for the product. Mass does not occur in this numeric entry test.

`Reserved bits profile count` checks the entries at indices strictly below
`count` (lines 118–119). It does not require room after the last query.
`Reserved.head` and `.tail` provide first-entry room and the remaining
reservation. `.mono` transfers this reservation to a smaller returned
profile. The empty sequence has no entry-room obligation. The final test
`reserved_iff_last` checks entry `count` for `count + 1` queries. Its reverse
direction uses monotone forecast growth and downward room transport.

The strict production check and all imported checks are clean. The canonical
build completed 1283 jobs. It replayed one older unused-variable warning in
`InternedFreshOrdinaryClosedCompletion`; the new source has no warning.
The 24 public pairs print explicit signatures and axioms. Three integration
pairs establish: a finite layout for any finite forecast; three successive
entry reservations from one original last-entry test, even when returned
profiles are smaller; and an arbitrary prefix/suffix reservation split.
All final probes use only standard Lean axioms. The failed production base
case and two failed integration attempts remain separate snapshots and logs.

This component does not prove physical profile fitting, operand availability,
original-source membership, closedness, cache provenance, or query semantics.
The serial producer must derive those facts at each actual return. The pure
forecast can be very large. No practical capacity or execution-time claim is
made. General selected constrained reduction and Haskell correspondence
remain separate parts of the full-library objective.
