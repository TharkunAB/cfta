# Final dependency cut audit

Status: READ-ONLY source analysis. No Lean declaration, compilation or proof credit. The countermodel below is a mathematical predicate sketch. No accepted-source reachability or Haskell defect is claimed. Source, original906 and5493 remain unchanged.

## Result

The actual local level constructions retain the proposed old/new cut. Their exported statements discard its witnesses. Current final Packet.ordered plus HeldFragmentHistory cannot recover it. The new actual ChildInputs lemma rules out the direct bad dependency at a genuine write, but it does not identify every final slot with such a write.

## Exact countermodel sketch

Use three singleton UF classes E=0, H=1 and T=2. Set counter=3, representatives=UnionFind.withInitialValues[0,1,2], obligations=[], recursionAncestry constantly[], and expansionAncestry=[]. Choose an arbitrary native handle h. Keep the same forest in both snapshots.

Before values:
- E: enumerated(hole H).
- H: unenumerated(some h)[].
- T: unenumerated none[].

After values:
- E: enumerated(hole H), unchanged.
- H: unenumerated(some h)[], unchanged.
- T: enumerated(hole E).

Before levels(E,H,T)=(0,1,1), frontier1. After levels(E,H,T)=(1,2,0), frontier2. Both stores are bounded, all allocated slots are live singleton roots, and both dependency graphs are stratified. Every pending bucket is empty, so PendingReferences and IncomingAvoid H hold. Old E and held H are protected. The only new stored fragment, hole E at T, directly avoids H. These facts satisfy the intended fields of HeldFragmentHistory H h before after; they do not give evaluator independence. With identical bases except the H choice, evaluateSlotsWith after roots base3 T evaluates through T→E→H and returns the changed H choice.

This disproves the predicate implication from independent before/after stratification plus HeldFragmentHistory to an old/new cut or evaluator noninterference. It is not a checked Lean counterexample and does not assert a full native Packet or a source run. In fact a genuine child result cannot produce hole E while E is protected and already expanded: PendingFragment would require E to resolve to a pending root.

## Where the useful facts are lost

- EnumerationOrder.lean18–22 defines only one-snapshot Stratified. It has no relation between separate witnesses.
- EnumerationOrder.lean83–145 constructs write_stratified. Local nextLevel93, increases99 and oldExpanded105 establish the useful preservation facts. The public conclusion89 exports only existence of a new Stratified witness.
- EnumerationStratifiedTransport.lean14–55 constructs stratified_preserved. nextLevel21–23 copies old expanded levels and assigns the frontier to every other representative. fixedExpanded24–28 remains local. Its public conclusion19 exports only existence.
- SourcePruningEnumerationRecursivePacket.lean21–34 packages ordered as an independent existential. captured_post retains the same packet, but callback_frame and receipt_packet package newly obtained existential witnesses.
- SourcePruningEnumerationSharedHookCertificates.lean45–50 retains only ∀initial level/frontier,∃final level,Stratified final at frontier+1. It does not retain old-level equality or a lower bound for newly expanded roots. The analogous NativeBranchCompletion.lean50–54 has the same limit.
- SourcePruningEnumerationSharedEagerReservation.lean2808–2815 calls write_stratified while constructing the after Packet, then stores only the existential result.
- SourcePruningEnumerationOpaqueSuffixIsolation.lean261–269 retains protection of old expanded slots and direct avoidance of H for new fragments. Its pending_target_avoids329–350 excludes the old-origin alternative for originally pending raw targets. It does not restrict the other holes in a new fragment to new classes.

## Existing authentic producer facts

EnumerationFragmentHistory.lean13–16 defines PendingFragment: every returned hole reaches a currently pending slot. pendingFragment_preserved39–71 transports this through old-expanded origin/protection; pendingFragment_write74–88 retains it through the target write.

EnumerationPendingFragmentExpandedAvoidance.lean8–22 proves pendingFragment_avoids_protected_expanded. Given the actual returned PendingFragment, an old expanded lookup and actual protection of that class, it derives fragment avoidance of that old class. No assignment or model is used.

The new owner-local actual_child_inputs_old_expanded_protection_and_avoidance at SharedEagerReservation.lean25837–25859 derives exactly this for every old expanded slot from the original Packet, literal pending target lookup and actual ChildInputs. It uses pending_inputs to derive the formerly missing all-old-expanded protection; that protection is not assumed. ChildInputs itself1188–1206 retains EnumeratedOrigin, PendingFragment and conditional root protection.

TupleInputs1488–1506 already retains unconditional all-old-expanded protection and PendingFragment for every returned child. Thus the same avoidance lemma applies to the assembled node fragment at actual_tuple_finalize_held_fragment_history21688–21775, after constructing PendingFragment.node from the actual returned children. The opaque counterpart24387–24452 has the actual child and finalizer receipts. Both finalizers retain the representative forest exactly and write only the captured target; target pending and old expanded lookups exclude target=old.

## Minimal authentic producer target

The desired output is a theorem about the SAME actual worker run and original Packet, not an extra assumption of the final goal. Select initial level0/frontier0 internally from packet.ordered. For every actual emitted output, derive ONE final level/frontier with:

1. Stratified output.core finalLevel finalFrontier.
2. For every old expanded slot, finalLevel old=level0 old.
3. For every live final root which was not expanded in the original store, frontier0≤finalLevel root.

Old expanded levels are below frontier0. Strict final dependency increase then excludes a hole from a new expanded root into any old expanded class. Safe storage and UF-compatible levels extend this conclusion to raw aliases. This is the genuine cross-snapshot witness missing from the exported receipts.

A smaller equivalent semantic producer is: every final expanded slot is either an unchanged original expansion, or its fragment avoids EVERY original expanded class, in addition to the already proved direct held-class avoidance. This supports dependency induction without explicit numeric cuts. It must be derived from actual writers and later class protection.

The existing local facts support both routes, but no searched public statement supplies the required whole-run witness. Merely opening Packet.ordered at each step cannot recover it. The universal FragmentHistory transport does not fix that loss, because it does not preserve the chosen old levels.

## Smallest next step

Expose the already proved chosen-level facts in NEW local order-transport/write corollaries, preserving existing public headers. First derive the old/new cut for ONE actual finalizer from genuine ChildInputs or TupleInputs plus the actual finalizer receipt. This is a concrete short producer, not a supplied closure law.

Whole-run use then needs one authentic connection. Either retain that chosen witness through the existing task/depth proof, or derive a final-slot birth receipt naming the actual captured/opaque finalizer and its genuine later protected suffix. Current HeldFragmentHistory.origin supplies only old-or-avoids, not that birth receipt. The new child lemma alone does not discharge this connection. Do not add cut, closure or model compatibility as a new premise of the original final completion target.

Once that authentic connection is proved, Root's final-snapshot evaluation algebra can use EnumerationPendingAssignment.evaluateSlotsWith_stable27–63 and EnumerationAssignment.fill_holes_congr17–35. This preserves one fixed final forest/store and changes only the pending held-class base choice. It proves raw-target independence; it does not by itself establish all removed Holds, guard preservation, native-domain membership or accepted original-root completion.
