# Recursive call measure for alternative merging

`MergedOrdinaryHeight.height` counts ordinary constructor layers. It stops at
Mu, explicit union, reference, and empty records. It reads the complete stored
children. It does not use cached Mu depth or identity age.

`child_lt` proves strict descent for a small group's direct child calls.
`closed_child` derives child closure from the ordinary parent's stored free
metadata. `guarded_column_ordinary` combines this fact with the actual
recursive-boundary guard. Every retained operand is then empty or ordinary.
The source `union` therefore uses its ordinary-edge concatenation branch.

`ordinaryUnion_bound` proves that branch's height bound through the actual
`makeNode` cache readback. `column_union_lt` gives strict descent for any
selected column from the original parent. Selection can remove arbitrary
operands. It cannot add one. Thus subsumption filtering, duplicate removal,
and the source group order cannot invalidate this measure.

`MergedMergeTermination.Step` contains the two recursive call forms.
`wellFounded` excludes an infinite chain of these calls, including calls in
different coherent cache states. `completes` supplies accessibility for any
finite required-call list whose members have one of those forms.

This is a branch-level source correspondence proof. It does not extract the
whole Haskell worker or discharge the separate `subsumes` helper calls. It
does not prove convergence when callers repeatedly merge or reduce the
result. A completed merge can increase the ordinary structure of its output
when it exposes retained recursive operands. The five-loop source diagnostic
found exactly that repeated-pass problem at upstream `4897831`.
