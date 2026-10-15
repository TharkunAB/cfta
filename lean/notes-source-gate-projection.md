# Selected projection from actual secondary gate traces

The [scoped class-query note](notes-source-gate-class-query.md) records the
later actual Operand/Fold/Seeded transfer, normalized fields, and gate-based
class refutation. The next target is the current reached lazy class prefix
and its gate readiness and memo invariants. Earlier limits below retain
their checkpoint scope.

Source main remains `525d722e`. The starting checkpoint is `5234cbab`.
Proof checkpoint `ea919bfa` is pushed to origin/formalize.
The [secondary gate note](notes-source-secondary-gate.md) records the earlier
head completion and exact head language. This work derives finite selected
projection, accepted-subtree inclusion, and physical annotation retention.
General scoped class composition and the whole caller remain open.

## Support at one completed gate heap

`SourceSecondaryGateProjectionSupport.Support` fixes one anchor heap G.
A value supports a natural path when it is closed, or is available in G
with an effect-free false node trace at that path. The closed alternative
does not require availability in G. Later exposure can produce closed
values. Current caller availability remains a separate premise.

`ordinary_selected_support` derives shorter support at every selected
ordinary child. Metadata fast paths derive closedness. Actual false row
scans retain each selected child certificate. The proof preserves the
original row and its child index.

`reachable_support` retains this invariant through actual epsilon successors.
Open Mu steps use the recorded unfolding and exact replay. Closed successors
remain closed. Actual traversal supplies availability at each reached source.
`head_selected_support` recovers raw row membership through makeNode,
canonicalization, and identifyNode readback. Actual nodeEdges origins then
supply support for each selected child in every rebuilt head row.
No cost heap, whole-head closedness, or output-language oracle is assumed.

## Actual anchor creation and endpoint closedness

`SourceSecondaryGateProjectionAnchor.node_anchor`, `path_anchor`, and
`class_anchor` start with actual completed false traces. Initial SemanticReady
and the older gate Ready derive both invariants in the final heap. Ready
includes the cost heap. The original operands remain available. The same
false trace then runs without a constructor effect at that final anchor.
Class anchors retain a certificate for every original path.

`support_endpoint_closed` derives closedness at node path []. This uses the
cost invariant only at G. Later caller and native heaps need not retain it.
No theorem derives whole-forest closedness from the false forest gate at [].

## Finite actual projection and effects

`SourceSecondaryGateProjectionComplete.node_complete` inducts on natural
path length. Ordinary rows recurse only through selected children. Recursive
heads use actual head completion, then selected support in the ordinary
result. Ordered row calls pass their exact returned heaps. The actual source
union joins the resulting closed operands.

The result is a complete Project receipt, Keeps, SemanticReady, availability,
and closedness. `node_verified` transfers these effects to any actual
completed receipt by uniqueness. `rows_verified` derives each intermediate
row effect. No final projection receipt or closed result is assumed.

`ForestSupport` keeps the source forest distinction. Its root case requires
closed operands. A proper path requires support only for its selected
original value. `forest_complete` and `forest_verified` retain missing
positions and the exact signed projection after natural-to-Int conversion.
These endpoints cover natural gate paths. They do not assert machine-Int
bounds or replace the existing signed negative-index results.

`false_node_complete` creates the anchor from the actual initial trace.
`false_path_complete` and `false_path_verified` do the same for proper
forest paths. They require path != []. Later caller heaps need current
SemanticReady, current operand availability, and growth from the completed
gate heap. They need no cost heap or whole-original-forest closedness.

## Independent language and physical annotations

`SourceSecondaryGateProjectionLanguage.node_included` and `forest_included`
retain each selected subtree of an independently accepted original term.
The recursive step uses exact actual head language. Ordinary steps keep
the selected row and child position. The actual union retains each accepted
projected term. `false_path_included` starts from the original false trace.
The theorem proves inclusion. Projection discards ancestor guards and can
accept additional terms.

`SourceSecondaryGateProjectionHeap.node_heap` and `forest_heap` preserve
every physical edge-annotation predicate in the exact actual returned heap.
Actual child effects supply intermediate readiness and retained operands.
The recursive branch uses actual HeadHeap preservation. `false_path_heap`
starts from the original false trace and current caller fields. No final
annotation heap or later cost heap is supplied.

## Next scoped class transfer

Add an Operand adapter for a natural path and its ForestSupport. The actual
force receipt exposes Forest. forest_verified and IdleReady.advance derive
the exact advanced native state. Retain its domain cache and both memo
tables. Transfer accepted subtrees and annotations through the same receipt.
Projection completion itself needs no native WordRanges premise.

Then induct over the actual Fold and Seeded schedules with one fixed G.
Keep current IdleReady, original Values, Grows G current.heap, and the
original path certificates. Each native Step receives the newly derived
closed projection and tail results. Its Keeps preserves the next inputs.
Use existing native annotation preservation for concrete top/conjoin fields.
Fold projects its head, evaluates its tail, then intersects. Seeded rotates
seed :: rest to rest ++ [seed]. Preserve that source distinction.

For gate-based refutes_decision, first assume ClassSat. Derive proper paths
with EqualityReduction.class_nonroot from Nontrivial and ClassSat. Only then
derive seeded effects, fields, and the common accepted subtree. Apply
Decision.sound last. False secondary traces and Nontrivial alone do not
exclude forest []. Do not add an unjustified global nonroot premise.

These statements will concern supplied completed scoped traces. Actual native
Step receipts include WordRanges. General fold/native completion, transfer
to the newer checked allocation state, lazy demand and sharing, whole caller,
recent waiting counts and template exclusion, broader APIs/runtime, and
all distinct exact Sized contracts remain separate full-library targets.

## Validation and preservation

The pinned full audit passes 2,042 jobs and 51,971 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. The existing unused
input warning remains. No new warning, admission, or axiom occurs.
Log: `/tmp/mcfta-gate-projection-audit-20261015.log`.

All prior Lean definitions remain byte-identical except two additive Audit
imports. All four Haskell package trees match `5234cbab`; their unchanged
checks were not repeated. All earlier proofs, repros, marked drafts, external
drafts, stashes, and other worktrees remain.
Start: `/tmp/mcfta-secondary-gate-checkpoint-20261015-1936/` (2,703 files).
Closing: `/tmp/mcfta-gate-projection-checkpoint-20261015-1953/` (2,709 files).
Script: `/tmp/mcfta-preserve-gate-projection-20261015.py`.
Weekly allowance is 86%. Full scope remains active.
