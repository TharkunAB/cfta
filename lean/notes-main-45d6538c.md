# Main 45d6538c: child-shape pruning in template exclusion

Main `45d6538c` is merged at `0694b6f9`. The refresh changes four existing
files. CI runs push checks on main and PR checks on pull requests. A newer
PR run cancels an older run. Main runs are not cancelled by that setting.

Template.edgeCopies now receives each child's literal root shapes. A shape
contains its symbol and arity. The interned path reads nodeEdges. The explicit
path reads transitionsOf. Required parts narrow the possible child shapes.
An empty base rejects all choices. A kept part survives only when at least
one common shape remains. Ground groups use the same nonempty-shape check.
Killed parts are filtered against the original child inventory.

## Checked component

`SourceTemplateShapeSplits` models the actual tail-first split order.
`splits_exact` and `splits_pairs` identify the optimized list as ordered
filtering of the prior choices. Surviving order and duplicates are retained.
Their initial fitting inventory must be nonempty, as required by the source
base and ground-group checks.

`accepted_child_splits` starts with actual explicit FTA acceptance. It derives
the accepted child's root shape and retains every filled old split choice.
`killedParts_exact` proves that removal of impossible killed parts preserves
avoidance. It uses the original inventory, as the source does.

The complete forced, mustDie, and ground-group edgeCopies pipeline remains
open. Physical nodeEdges inventory transfer, part-index bounds, whole
exclusion, and runtime correspondence remain separate obligations. Many
compatible open parts can still produce exponentially many choices.

## Validation

The strict Nix build and all six suites pass: 736 examples and the golden
check. Fourmolu passes both changed Haskell files. Cabal-gild passes all four
active packages. The full Lean audit passes 2,137 jobs and 53,195 dependency
checks. It has no new warning or forbidden axiom.

Equality, Interned.fromRows, Sized, GHC, and curried production bodies did
not change in this refresh. The local equality repair remains intact.
