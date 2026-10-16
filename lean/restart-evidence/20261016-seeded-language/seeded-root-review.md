# Checked seeded language review

Date: 2026-10-16 07:59 CEST.
Read-only review. No build or source edit ran.

## Verdict

No material defect found. The module derives a whole checked seeded-fold
receipt and common-subtree inclusion under its stated initial warm
invariants, anchored path support, proper paths, and reached word ranges.
It does not assume a future result law, next inventory validity, successful
recursive query, or final cache invariant.

## Actual order and state

The source uses `getPath` for each class path and
`intersectList (n : ns) = foldr intersect n ns`
(`cfta/src/Data/CFTA/Equality/Operations.hs:219-230`). For three projections
`[a,b,c]`, the fold is `intersect b (intersect c a)`.
`Seeded.nonempty` and `seeded_complete` use the literal `rest ++ [seed]`
rotation. They preserve the source fold expression rather than replacing
it with an associative or commutative permutation.

`fold_complete` follows head projection, completed tail fold, then the
actual checked request of the head value and tail result (lines 93-125).
It threads the literal returned checked states. No native table or
equality-operation cache is reset. The returned `Fold` records the actual
query trace. `Seeded.receipt` and `false_class_receipt` use determinism to
identify the entire actual returned state, not only the result value.
This explicit completed graph schedule is not a GHC lazy-forcing theorem.

## Input models and warm cache laws

`InventoryState.Inventory` stores concrete source records, finite closed
roots, and their residency/original witnesses. Its input model is computed
from those records. `InventoryState.At` contains initial contextual cache
laws, all-phase operand/seen coverage, source heap growth, and issued
history (lines 25-52). These are legitimate explicit warm-state premises.
They do not contain a result for the current fold or a completed callback.

Projection changes only the physical heap and retains the native cells.
`At.advance` therefore retains the same input interpretation and contextual
laws. The proof supplies the derived actual machine extension. A native
query then uses `InventoryState.query_complete` on its actual entry heap.
That endpoint derives the next inventory with roots equal to the previous
roots followed by the actual closed head and tail operands. It derives
next contextual laws and all-phase coverage from actual query completion.
The next inventory is not supplied by the fold theorem's caller.

The head value's availability is transported through the actual tail
effects. Its closedness is an immutable value fact. The tail's availability
and closedness come from the induction receipt. These facts admit the two
actual native operands. No desired intersection result supplies admission.
The native query's independently derived exact physical meaning combines
the two subtree-inclusion facts at line 125.

## Domain and scope checks

The original forest requires only `Values` at the current heap. It need not
belong to the closed-root inventory. Selected projections derive their own
closed results from anchored `PathSupport`. Unrelated original siblings
can remain open. The proof does not replace this domain with whole-forest
closedness.

`Includes` is common selected-subtree containment, not projection language
equality. It uses independent accepted original terms and the same selected
part at every literal path (lines 37-44). Proper paths are explicit. The
empty seeded list returns empty and provides inclusion only under the
impossible premise that the list is nonempty (lines 140-144). Thus empty
lists and forest-root projection do not produce a vacuous language claim.

`false_class_complete` derives support and anchor effects from the actual
current-secondary gate. It advances the same checked state to the actual
gate anchor, retains `At`, then completes the fold. Its returned physical
effects include the gate prefix from the original pre-gate state.

`FoldRanges` remains an explicit machine-capacity condition. It quantifies
over actual operand/tail prefixes but does not assert their existence or
their language result. The fold induction constructs each prefix before
using the corresponding range obligation. It is not a future-success
oracle. Deriving these range plans from a larger caller remains separate.

## Retained coverage limits

The conditional whole checked seeded-fold language component is now
established. Whole caller/scan soundness, class acceptance witnesses,
emptiness-memo refutation composition, global gate memo integration,
machine-key capacity discharge, and GHC/runtime transfer are separate.
Initial `Good`, physical `Ready`, scoped and idle native caches, and `At`
remain explicit. The result does not admit arbitrary cross-model warm
caches without these concrete initial invariants.

## Evidence inspected

`seeded-language-build-2.log` records terminal success for 1227 jobs.
Only the preexisting unused `inputs` warning appears. This review did not
repeat that build.

```text
9bdf2f2d893aaf6667e71f5cc062162b3622bfae62397924a818ae199dddd598  SourceCurrentAllocatedSeededLanguage.lean
4944b25b19d4a897a49faedff94205058d4fbcf0e0fecafbcc40bb3d026998fc  SourceCurrentAllocatedNativeInventoryState.lean
2d191adfef1d0e17b085f43c10c934be60ec9b274259b1d4a2730b9ff050021f  SourceCurrentAllocatedSeededOperandLanguage.lean
```
