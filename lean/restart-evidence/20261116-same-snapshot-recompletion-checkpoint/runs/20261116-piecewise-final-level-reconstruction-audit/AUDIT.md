# Piecewise final level reconstruction

Status: UNPROVED mathematical design audit. No Lean proof or actual worker
producer is claimed. No Source file, runtime budget, or cap changed.

## Conditional hypotheses

Let `before` have `Stratified before L0 F0`. Let `after` have Safe and ANY checked
`Stratified after L1 F1`. For every original expanded slot and fragment, require
the FULL existing `Protected slot before after` receipt. Its value, root, and
class-equivalence fields are all relevant.

Require this stronger birth receipt for every final expanded slot:

```
after.values[slot]? = some (enumerated fragment) ->
  before.values[slot]? = some (enumerated fragment) OR
  forall oldSlot oldFragment,
    before.values[oldSlot]? = some (enumerated oldFragment) ->
    FragmentAvoid after.representatives oldSlot fragment
```

This is an explicit LOCAL mathematical hypothesis. It is NOT yet a whole-worker
producer, and must not become a new external premise of the original goal.
The current held-only birth receipt does not imply it.

Initial Safe is additionally required for the allocated raw monotonicity
corollary below. The initial Packet supplies it. Keep this requirement separate
from the piecewise stratification argument.

## Construction

Use exactly the parent's proposed class predicate and formula:

```
Old uv := exists oldSlot oldFragment,
  before.values[oldSlot]? = some (enumerated oldFragment) AND
  SameClass after.representatives oldSlot uv

Lnew uv := if Old uv then L0 uv else F0 + L1 uv
Fnew := F0 + F1
```

Class membership is essential. Testing only whether `uv` itself has an old
expanded lookup is insufficient for eliminated raw aliases.

The stated hypotheses suffice for `Stratified after Lnew Fnew` and for preserving
the level of EVERY original expanded class member. There is no requirement to
transport one particular final level witness through the worker.

## Exact case argument

1. `Old` is invariant under final SameClass. In an old class, use one protected
   old anchor. Its classes field transfers BOTH alias memberships to the initial
   forest. Initial `L0` class consistency therefore proves final consistency of
   the old branch of `Lnew`. In a non-old class, final `L1` consistency proves it.
2. An old expanded anchor is still expanded with the SAME fragment, and is a
   final root. Final Safe makes a live final slot in that class the identical
   root. Thus an old-class final expanded slot has its exact original fragment.
3. Its level is `L0 slot < F0 <= Fnew`. For an old-class hole, retain the initial
   strict dependency. For a non-old hole, `Lnew hole >= F0 > L0 slot`.
4. A non-old final expanded slot cannot use the original-lookup alternative of
   the birth receipt. Its fragment avoids EVERY old expanded class. Every raw
   hole is therefore non-old. The final strict inequality under `L1` survives
   adding `F0` to BOTH sides. Its level is below `F0 + F1`.
5. A final pending slot cannot be in an old expanded class: final Safe and the
   protected old root would identify their slots, contradicting their stored
   constructors. Its new level is `F0 + L1 slot = F0 + F1`.

This uses `HasHole` for ALL raw hole IDs, not just allocated holes. Both initial
and final Stratified.expanded quantify all such holes. No hidden fragment-bound
hypothesis is needed for these cases. Protected.classes also quantifies all raw
IDs, so eliminated aliases and unallocated IDs require no special lookup claim.

The exact pending equality is why the new frontier is `F0 + F1`. Adding one only
to the frontier is wrong. Adding a common extra constant to every shifted level
AND that frontier would work, but is unnecessary. If F0 or F1 is zero, the same
proof works; an expanded slot below a zero frontier is impossible.

## Raw bounds and initial inputs

With INITIAL Safe, every `uv < before.counter` has an allocated live initial
representative. Initial Stratified says its level is below F0 if expanded, or
exactly F0 if pending. Initial class consistency gives `L0 uv <= F0`.
For an old class the new level is equal to L0. Every other class gets at least
F0. Hence allocated raw levels do not decrease. This argument does not claim
monotonicity for arbitrary unallocated IDs.

For a historical input bucket use the genuine `InputsPending before bucket`
receipt. It excludes every raw target from every original expanded class.
Protected.classes carries that exclusion to the final forest. Every raw target
is non-old and has `F0 <= Lnew sc.var`. No assertion that `sc.var` itself has a
pending lookup is needed: it may be an eliminated alias. The source route is
`Packet.pending` plus the ORIGINAL stored bucket and `pending_inputs`, together
with the actual raw bound/read receipts when allocation is needed.

Exclusion from the HELD class is separate. Use actual selection/IncomingAvoid
and protected held-class transport. Exclusion from old expanded classes does
not imply exclusion from a held class that was originally pending.

## What still requires actual execution proofs

The strong new-to-ALL-old-expanded avoidance receipt is still a whole-worker
producer gap. The local actual ChildInputs producer and protected old slots are
useful primitives. The current whole-worker HeldFragmentHistory origin only
mentions the ONE held class. It cannot silently be strengthened to all old
expanded classes.

Old-class preservation and strong births compose in principle: protected values
retain the original old slots at intermediate snapshots; protected classes
transport their avoidance; a later new birth avoids all intermediate old slots,
which include the original ones. An actual induction must still prove these
facts through the real tuple, finalize, callback, and recursive worker branches.
No such induction is provided here.

For the existing cut algebra, the strong receipt establishes old/new block
separation. The separate existing held-origin receipt supplies held avoidance.
The original source compatibility, target TypeIn, current native domains,
residuals, guards, and ALL historical obligations remain distinct obligations.

## Optional smaller kept-set route

Once BOTH strong all-old birth and the held-only birth receipt are genuinely
produced, the one-clear kept set can be defined directly as
`not Old uv AND not SameClass after.representatives held uv`.
It is a union of final classes. Any expanded root in it must be a new birth.
Its holes avoid all old classes and the held class, so it is dependency closed.
`InputsPending` plus held separation puts every removed raw target in that set.
Thus that one-clear use can bypass even the piecewise level reconstruction,
while retaining ANY existing final Stratified witness for finite evaluation.
This route has the SAME still-missing actual strong-birth producer. It is not a
new global closure premise or a proved alternative theorem.
