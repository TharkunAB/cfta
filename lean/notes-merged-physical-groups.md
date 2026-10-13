# Physical alternative-group construction

The new group proofs execute the two-cache constructor computations. They
use the current source threshold from `Interned/Operations.hs`: a group of
at most four canonical rows retains each guard; a larger group creates one
unconstrained row from the child columns.

`MergedPhysicalGroupCalls.mapCalls_correct` threads the actual state through
ordered child requests. It derives the final prepared context, availability
of each returned record, and positionwise language coverage. Cache growth
preserves the language of earlier available records. Each child certificate
describes only that recursive call's actual input and output states.

`MergedPhysicalGroupEdges.smallEdge_correct` and `largeEdge_correct` execute
the child calls and actual `makeEdge`. They derive complete readback of the
symbol, guard, and ordered children. The small branch retains the original
guard. `smallEdge_setChildren` proves that the source's actual `setChildren`
continuation takes its equal-arity direct interning branch. The large branch
uses the supplied unconstrained guard. Its accepted child row follows from
`MergedAlternativesGroups.columns_cover` and the actual column results.

`MergedPhysicalGroup.group_correct` combines both threshold branches. Its
output has at most four row occurrences before parent normalization. Every
original row has an actual returned row with the same symbol and arity.
The returned guard is the original guard or the unconstrained guard. The
returned row covers the original row's finite language in the final cache.
`build_covers` then executes actual `makeNode` and proves group language
coverage for the returned parent record.

`MergedPhysicalGroupColumns.checked_selected_exact` uses the physical
subsumption checker to justify the source filter. It retains closed Mu
operands, applies the free-variable gate to the narrow operand, and removes
only operands covered by successful comparisons. Source first-identity
duplicate removal preserves complete resident records. The result is an
exact selected-column language equation. `checked_retained_union` executes
the repaired `createUnion` branch and derives that exact equation at its
actual returned cache. No semantic filter or constructor equation is a
premise of these two public theorems.

`MergedPhysicalGroupColumnWorker.checked_column_correct` combines the
checker, filter, and all three `mergedUnion` branches. A singleton returns
the selected record. A recursive or union boundary uses the retained union.
All other closed operands are ordinary or empty. Their actual ordinary
union has at most the greatest input ordinary height. The final recursive
merge call therefore needs a certificate only at that smaller height.
The proof does not assume that the returned merged value has a smaller
height. `child_step` and `selected_column_step` connect the corresponding
requests to `MergedMergeTermination.Step`.

`MergedPhysicalGroupRoot.groups_correct` sequences every group and retains
earlier returned edge languages through all later effects. Its `build_covers`
executes actual parent construction and proves coverage of the original
ordinary root. `grouped_root_covers` adds an explicit source grouping
contract: flattening the groups permutes the original canonical rows, and
each group equals the original row list filtered by its complete symbol and
arity key. This pins row order within a group and prevents a large source
group from being split into small groups. The outer HashMap group order
remains an explicit parameter.

The root result derives final `Context` and `Available` at the actual
returned state. It does not use a separately prepared proof cache as the
runtime continuation state. Its remaining premises are local recursive
child or column certificates, the source grouping contract, and the guard
interpretation. The column worker supplies the primitive column branches
and restricts its recursive certificate to a bounded height. These parts
are not yet assembled into one extracted state-adaptive recursive merge
worker. The comparison snapshot in `checked_column_correct` is explicitly
the actual column-call state. The group combinators currently accept finite
`Work` callbacks. Connecting that state-specific selection to the recursive
callback is a remaining composition step.

The checker statements hold at any supplied finite fuel. A source replay
must choose the proved inventory saturation bound to identify its complete
comparison result. Fuel below that bound can retain additional operands.
The group bound counts the supplied physical canonical rows, including
distinct raw guards. It does not count guard meanings or prededuplicated
syntax occurrences. Full equality fixed-point termination remains open.

Validation on 2026-10-13: Lean 4.34.1 compiled all six modules and their
dependencies. These files make no production source change. Existing
Haskell validation therefore remains the 620 examples at `c76d1ec`.
