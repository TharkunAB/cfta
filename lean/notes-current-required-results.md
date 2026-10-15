# Structural domains after actual required-path reconstruction

`SourceCurrentRequiredResultDomain` and
`SourceCurrentRequiredResultPreservation` extend the actual open-input
required worker. Source main `9a2f9bea` leaves that worker unchanged.

## Domain

`NodeDomain needed value` permits a closed value at any requirement. It
also permits a nonterminal ordinary node whose selected children have the
domains of their exact stored requirements. Unselected siblings can remain
open. The ordinary alternative requires a nonempty local requirement.
Thus an empty local requirement implies actual free-list closedness.

`ForestDomain`, `RowsDomain`, and `ChildrenDomain` retain original child
positions and list offsets. They have no earlier heap parameter. Closed
Mu and union records use the closed alternative. Their membership does not
assert that a secondary gate returns false.

`makeNode_domain` follows the actual canonical edge list and complete-record
readback. It includes interning hits. Reconstructed open values do not need
to exist at an earlier gate heap.

## Actual graph preservation

`node_domain` derives the result domain from the actual `RequireNode`
graph, valid nonnegative Needed, initial semantic and availability facts,
and original `NodeTips`. The empty identity case uses the terminal
certificate. Selected child requests decrease Needed size. Recursive Head
results use their actual exposed row children and constructor histories.
No future result-domain premise is supplied.

`children_domain` and `rows_domain` retain the actual returned positions
and constructor fields. `requireAll_verified` returns actual constructor
history, semantic readiness, available results, and their `ForestDomain`.

`NodeDomain.tip_closed` and `forest_tip_closed` connect every maximal tip to
the existing `SourceEqualityProjectionPathDomain` predicates. They need
only final semantic readiness and actual value availability. This gives
the existing path-local projection worker a domain on rebuilt results.

`SourceCurrentClassRequired.scan_required_complete` derives this result
from the actual successful scan and original selected classes. It retains
the literal scan-final heap between the stages.

## Remaining obligations

A shorter original path can stop being maximal when another path extends
it. The structural tip domain alone does not prove closedness at that
shorter endpoint. Conditional whole-node closedness preservation is
already proved by the older required execution theorem. That fact must be
carried through the original shorter path occurrences.

Shared-target construction and later class edits still need domain
preservation. Required and fallback calls still need cost, field, and global
memo composition. This proof does not establish path existence at missing
root positions, whole caller completion, or physical Haskell execution.
