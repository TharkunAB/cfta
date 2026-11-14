# Canonical waiting counts and selected bucket incidence

Status: SOURCE AUDIT. No new Lean theorem was compiled or installed. No source
execution or reachable counterexample is claimed. The full original goal remains
open. This packet adds no premise to that goal.

Date: 2026-11-14 18:27 CET.

## Result

The canonical waiting index does not identify the suspended targets in one
selected bucket. It counts references to each target class across all pending
slots. The existing selection theorem gives the opposite of the proposed
selected-root equality: no stored suspended target is in the selected root's
class. This includes every target in that selected root's own bucket.

This result is already public in checked source. Do not add a duplicate producer.
Use `SourcePruningEnumerationSelection.unblocked_avoids` and `incoming`, or the
combined actual restart producer `SourcePruningEnumerationRestart.selected`.

The index does not recover the missing target incidence for historical clears.
Clearing a bucket removes its outgoing references from the index. Some of those
target classes can then become eligible for later selection. A finite model must
still satisfy the removed path constraints under the same assignment that
satisfies those later choices.

## Exact existing producers

All paths below are relative to the repository root.

| Source | Exact fact |
| --- | --- |
| `lean/MicroCFTA/EnumerationCanonicalWaiting.lean:17` | `canonicalValue` retains each trie and replaces its target variable by `roots sc.var`. |
| `lean/MicroCFTA/EnumerationCanonicalWaiting.lean:35` | `Correct` is the exact global occurrence count after that replacement. |
| `lean/MicroCFTA/EnumerationCanonicalWaiting.lean:106` | `support_exact`: a key is present iff some stored pending slot has some suspended reference to that root. |
| `lean/MicroCFTA/EnumerationSchedule.lean:290` | `class_iff`: two variables share a forest class iff their canonical roots agree. |
| `lean/MicroCFTA/SourcePruningEnumerationSelection.lean:11` | `offered`: actual selection returns an allocated candidate whose waiting entry is absent. |
| `lean/MicroCFTA/SourcePruningEnumerationSelection.lean:25` | `unblocked_avoids`: an absent waiting entry excludes every stored bucket target from that selected root's class. |
| `lean/MicroCFTA/SourcePruningEnumerationSelection.lean:44` | `ready`: actual native flags, canonical counts, and pure selection establish `EnumerationDriver.Ready`. |
| `lean/MicroCFTA/SourcePruningEnumerationSelection.lean:74` | `unblocked_incoming`: the same exclusion holds over every stored reference. |
| `lean/MicroCFTA/SourcePruningEnumerationSelection.lean:88` | `incoming`: actual native selection establishes that global incoming-reference exclusion. |
| `lean/MicroCFTA/SourcePruningEnumerationRestart.lean:52` | `selected`: actual restart expansion combines readiness, incoming exclusion, the exact stored bucket, and its closed available native node. |
| `lean/MicroCFTA/SourcePruningEnumerationClear.lean:11` | `complete`: actual clear subtracts the full bucket from canonical counts, makes the cleared recursive boundary ineligible, and retains the exact invariants for remaining references. |
| `lean/MicroCFTA/SourcePruningEnumerationParkedLanguage.lean:68` | `checkRepeated_true_satisfies`: the exact reverse semantic requirement is satisfaction after clear plus all removed `Suspended.Holds`, under one assignment. |

The source pins in this directory identify the versions read for this audit.

## What follows directly from actual bucket retrieval

Let `u` be the actual selected root, let its stored value be
`unenumerated (some h) scs`, and let `roots` satisfy the real `Roots` invariant.
Under the actual canonical count and selection invariants:

1. `waiting u = none`.
2. For each `sc` in `scs`, `waiting (roots sc.var) != none` before the clear.
   The witness for `support_exact` is the actual selected slot and that actual
   suspended entry. This uses no semantic assignment.
3. For each such `sc`, `roots sc.var != u`. The stronger existing result states
   `not (UnionFind.SameClass forest u sc.var)`.
4. If two target roots happen to agree, `class_iff` identifies their alias class.
   It does not assert that the roots agree. Distinct targets in one bucket are
   allowed by the count invariant.
5. The index retains the number of references to a target class. It does not
   retain their owning slot, their trie shapes, or their earlier provenance.

Thus a theorem stating that every selected bucket target has canonical root `u`
contradicts the actual selected-state invariant whenever the bucket is nonempty.
A theorem stating that all targets share some other root also does not follow
from counting. For example, two references with distinct targets contribute one
count to each of two distinct root keys. This is an observation about the count
definition, not a claimed source-reachable execution.

The actual selected prefix reads the full bucket unchanged:
`SourcePruningEnumerationSelectedStep.runPrefixWithNarrow` matches the successful
`getValue` result and passes that same `scs` to `checkRepeated`. It applies no
additional filter that identifies the suspended targets.

## What alias satisfaction supplies

`UnionFind.Satisfies` says that an assignment gives equal terms to variables in
one forest class. With `Roots`, it therefore gives
`rho (roots sc.var) = rho sc.var`. This justifies interpreting an existing
suspended constraint through its canonical target.

This implication requires an assignment. It does not construct one. It also
does not identify different root keys or show that later domain restrictions
have a common finite inhabitant.

If two suspended entries have the same represented paths and their target roots
agree, their `Suspended.Holds` predicates agree for one source term under any
assignment that satisfies that forest. The missing input is the target-root
agreement. The canonical count invariant does not provide it for a bucket.

For two obligations with the same nonempty trie and the same source term,
satisfaction forces their assigned target terms to agree. This is a consequence
of already satisfying both obligations. The waiting index does not establish
the existence of such a simultaneous assignment.

## The consequence of clearing

`SourcePruningEnumerationClear.complete` gives exactly

    waitingAfter = EnumerationCanonicalWaiting.count roots (-1) scs waitingBefore

and proves the resulting counts correct for the actual updated slot array.
If other references to a target class remain, that target stays blocked. If no
references remain, its waiting key disappears. Its eventual eligibility also
depends on its native candidate flag.

The removed bucket's raw target IDs and paths are consequently absent from the
remaining index relation. Neither `Correct` nor `Roots` can recover an erased
reference from the remaining count. The historical obligation still concerns
those exact IDs, interpreted through the later alias forest and the one final
assignment.

This is the useful direction for the next proof: derive the historical path
incidence from the actual branch operations, then construct a joint model that
keeps it valid while the newly eligible targets are expanded or merged. Merely
proving that the remaining index is correct does not establish that model.

## Haskell check

`cfta/src/Data/CFTA/Enumeration.hs:448` implements the same count update.
`writeUVarValue` removes each lost reference at
`UnionFind.root (scGetUVar sc) uf` and adds each gained reference there.
`findExpandableUVars` at line 835 subtracts the waiting key set from the
expandable set. It does not group a selected slot's constraints into one class.

The repeated branches near lines 1006 and 1542 clear the full bucket and recurse.
These reads support the index interpretation above. No new Haskell defect or fix
was established by this bounded audit.

## Scope and next work

`INCIDENCE-TARGET.md` states the exact missing semantic incidence requirement.
It retains the original existential joint-model quantifiers. It does not supply
a history certificate or ask for additional runtime ancestry fields.

No arbitrary `Mu` model or closed proper-cycle counterexample was reproduced.
No new Lean candidate is frozen: the useful local producer already exists, and
the desired stronger alias statement does not follow from its hypotheses.

All original boundaries remain: one finite accepted completion of the same
original emitted root, one assignment for domains, aliases, paths, fragments,
residuals and historical cleared obligations, actual readback, and backward
recompletion. The broader typing, depth, LPO, language, stream, node-count,
count/weight/training, rank inverse, host-bound and compiled Haskell objectives
also remain open where the main handoff states they are open.
