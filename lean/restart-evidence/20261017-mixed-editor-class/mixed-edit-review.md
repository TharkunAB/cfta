# Mixed editor cap verification

The frozen production source is `lean/MicroCFTA/SourceCurrentConstrainedCapMixedEdit.lean`.
Its SHA-256 is `c4a225deb992028f5fb642210624b94107d766dd8bd7f37ce8eba351fbd37fb3`.
The module has 380 lines. Canonical build `canonical-mixed-edit-1.log` passed all 1431 jobs.

## Contract

`node`, `children`, `rows`, and `list` verify the same supplied strict edit reads.
Each theorem takes initial physical readiness, actual input availability or residency,
selected path domains, causal `MixedShared.Stored`, and cap bounds for the captured
original forest and the current immutable inputs. Node edits also require a retained
leaf. All constructors retain the exact checked state, target slots, completed Merge
table, and global memo indices from the supplied reads.

`outputDepth captured input edits = input + captured + sizeOf edits` and the child-map
variant are static logical bounds. Both definitions are noncomputable. They are not
executable capacity estimates, instruction bounds, or constructor allocation budgets.
The proof derives these bounds from the initial syntax. It does not take a desired
result cap or a recursive callback law as an input.

## Actual branch checks

- The leaf branch uses `MixedShared.leaf_receipt` at its literal reached state.
  The initial record domains supply only the other selected operand paths.
  Their target depth is at most the captured input depth.
- Empty, ordinary, and recursive Head branches use their actual constructor or Head
  return. The Head theorem retains the same input cap and causal stores.
- Selected children retain their original ordered input. The first return supplies
  the next readiness, global memos, and stores. Signed lookup membership bounds each
  child syntax by its parent map syntax.
- Rows retain the original full guard and ordered arity. Child caps reserve the
  parent ordinary layer. Zero-depth original rows use their hereditary guard law.
- List reads retain the same captured original forest. The ignored list-root leaf
  branch retains the original values and stores.

There is no hereditary `AtLeaves` premise, whole captured-forest closure premise,
future leaf certificate, or future result/store assumption. Selected ordinary paths
can leave unrelated open siblings untouched. Recursive Head exposure still uses its
actual selected closure requirement.

## Imported checks

`mixed-edit-public.lean` checks all six public declarations with explicit signatures,
proofs, universes, deep terms, and axiom reports. `mixed-edit-public-1.log` passed with
no diagnostics. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

`mixed-edit-kernels.lean` has two strict imported integrations. Final log
`mixed-edit-kernels-4.log` passed with no diagnostics.

1. `constructed_warm_nonplain_leaf` starts with an actual present slot and its initial
   causal stores and physical receipt. It proves that a nullary ordinary input with
   a failing raw guard is not hereditary, derives its cap at depth one, and constructs
   its own finite native leaf query and node reads. The resulting store and cap belong
   to that same returned state. No completed Leaf or query is a caller premise.
   The initial slot history is a past-state premise. The test does not construct that
   earlier slot miss. Initial numeric node, edge, and finite domain-inventory headroom
   derive the reached word checks. This is not a cumulative allocation reservation.
   No whole captured-forest closure is required.
2. `two_actual_edits` consumes two supplied read prefixes. It derives the second
   entry's readiness, availability, globals, selected path safety, stores, and input
   caps from the first exact return. It takes no intermediate cap/store law.

The failed production direct attempt and all failed integration attempts retain exact
source snapshots and logs. Integration attempts one and two are identical; a local
path error prevented the intended edit before attempt two. Attempt three fixed the
entry type and instance scopes. Attempt four supplied the missing empty-child
projection reduction. The frozen production source did not change during these tests.

## Scope

This component proves cap and causal-store preservation for supplied completed strict
edit graphs. The first integration constructs one admitted warm-slot leaf execution.
It does not prove general editor completion, mixed selected termination, or allocation
headroom for every edit. It does not prove whole-library Haskell correspondence.
