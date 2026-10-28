import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationChildBoundedResources
import MicroCFTA.SourcePruningEnumerationEdgeScalarBounds

/-!
# Resources through actual prepared opaque and terminal dispatch

The original stored handle is separate from the prepared value. General
child completion covers terminal buckets. No ProperState premise is used.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "receiptAdvance" => SourcePruningEnumerationNativeBranches.advance
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original resources derive the exact prepared receipt without a future cache invariant. -/
theorem opaque_complete_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (target handle : Nat) (scs : List Suspended)
    (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid target before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (bounded : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (scs.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (reached : Caller (bits + 2))
      (saved : Queries) (final : Memos) (next : Inventory),
      (∀ extra, SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        target scs value caller before memos.query = some receipt) ∧
      Post formulas solver next caller reached final ∧ final.query = saved ∧
      receiptAdvance receipt = some (reached, saved) ∧
      Admitted target receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
      Fits (advance seed (scs.length + 1)).2 reached.checked ∧
      Heap (fun guard => guard ∈ (advance seed (scs.length + 1)).1) reached.checked.native.machine.heap ∧
      ((∃ fragment after, receipt = .complete fragment reached saved after ∧
          Packet formulas solver next reached final metadata after ∧
          after.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound after.core ≤ suspendedBound before.core + scs.length) ∨
        (∃ after outer waiting, receipt = .stopped []
          (.ok (some []), reached, saved, outer, waiting) (some after) ∧
          after.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound after.core ≤ suspendedBound before.core + scs.length) ∨
        receipt = .rejected caller memos.query before) := by
  by_cases empty : value = .empty
  · subst value
    refine ⟨0, .rejected caller memos.query before, caller, memos.query, memos, inventory,
      ?_, Post.refl packet.context, rfl, rfl, packet.valid, packet.pending, trivial,
      bounded.mono (SourcePruningEnumerationIncomingReservation.advance_profile_ge seed _),
      ?_, Or.inr (Or.inr rfl)⟩
    · intro extra
      simp only [SourcePruningEnumerationSelectedOpaqueDispatch.run, ↓reduceIte]
    · intro key edge found
      exact SourcePruningEnumerationIncomingReservation.advance_alphabet_ge seed _ (known key edge found)
  · obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
    have bucketBound : ∀ sc ∈ scs, sc.var < before.core.counter :=
      ready.safe.1.values _ (List.mem_of_getElem? stored)
    have avoids := ready.avoids handle scs stored
    have pendingInputs := EnumerationReferences.pending_inputs before.core packet.pending
      target (some handle) scs stored
    obtain ⟨r, n, p, h, k, raw, reached, middle, saved, final, next, afterRoots, outer, waiting,
      childRun, post, query, growth, middlePaths, middleStorage, middleRealized, middleCounts,
      middleFlags, origin, protects, references, pendingHistory, shape, afterFits, afterKnown,
      counterBound, massBound⟩ :=
      SourcePruningEnumerationChildCompletion.complete_with_fragments_cache_bounds seed formulas solver inventory
        caller before checkEmpty scs value roots memos packet.context packet.safe paths counts flags
        realized bucketBound pendingInputs available closed bounded reserved known
    let childBound := r + n + p + h + k
    have childAt (w : Nat) (large : childBound ≤ w) :
        SourcePruningEnumerationChildDispatch.run checkEmpty w w w w w scs value caller before memos.query =
          ((.ok (some raw), reached, saved, outer, waiting), some middle) := by
      have rl : r ≤ w := by dsimp [childBound] at large; omega
      have nl : n ≤ w := by dsimp [childBound] at large; omega
      have pl : p ≤ w := by dsimp [childBound] at large; omega
      have hl : h ≤ w := by dsimp [childBound] at large; omega
      have kl : k ≤ w := by dsimp [childBound] at large; omega
      have actual := childRun (w - r) (w - n) w w (w - k) pl hl
      simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using actual
    rcases shape with rejected | ⟨fragment, singleton, middleSafe, fragmentBound, fragmentPending, fragmentSeparate⟩
    · subst raw
      refine ⟨childBound, .stopped [] (.ok (some []), reached, saved, outer, waiting) (some middle),
        reached, saved, final, next, ?_, post, query, rfl,
        ⟨afterRoots, middlePaths, middleStorage, middleRealized, middleCounts, middleFlags⟩,
        pendingHistory packet.pending, trivial, afterFits, afterKnown,
        Or.inr (Or.inl ⟨middle, outer, waiting, rfl, counterBound, massBound⟩)⟩
      intro extra
      simp only [SourcePruningEnumerationSelectedOpaqueDispatch.run, ite_eq_right empty,
        childAt (childBound + extra) (by omega)]
      cases value <;> simp_all
    · subst raw
      have frame := protects target ready.inside ready.root avoids
      have middleStored : middle.core.values[target]? = some (.unenumerated (some handle) scs) :=
        frame.value.trans stored
      obtain ⟨finalFuel, after, finalRun, _finalRaw, core, finalStored, _flag, _waiting,
        afterPaths, afterCounts, afterFlags, afterStorage, afterRealized, safeFinish⟩ :=
        SourcePruningEnumerationFinalize.complete reached.checked.native.machine.heap middle target fragment
          (.unenumerated (some handle) scs) middleStored afterRoots middlePaths middleCounts middleFlags
          middleStorage fragmentBound middleRealized
      have afterSafe := safeFinish middleSafe frame.root
      have separate := fragmentSeparate target ready.inside ready.root avoids
      have finalPending : PendingFragment after.core fragment := by
        rw [core]
        exact pendingFragment_write middle.core target fragment fragmentPending separate
      have incomingMiddle := SourcePruningEnumerationNativeReferences.incoming_preserved
        before.core middle.core target scs incoming avoids frame.classes references
      have afterPending : EnumerationReferences.PendingReferences after.core := by
        have written := EnumerationReferences.setValue_pending target fragment middle.core
          {middle.core with values := middle.core.values.set target (.enumerated fragment)}
          (pendingHistory packet.pending) incomingMiddle ((EnumerationDriver.modify_success _ _ _).mpr rfl)
        rw [core]
        exact written
      have orders : ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1) := by
        intro level frontier ordered
        have enumProtects : ∀ held old, before.core.values[held]? = some (.enumerated old) →
            EnumerationDriver.Protected held before.core middle.core := by
          intro held old oldStored
          obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held old oldStored
          exact protects held inside root (pendingInputs held old oldStored)
        obtain ⟨middleLevel, middleOrder⟩ := EnumerationOrder.stratified_preserved before.core middle.core
          middleSafe level frontier ordered origin enumProtects
        obtain ⟨nextLevel, nextOrder⟩ := EnumerationOrder.write_stratified middle.core middleSafe middleLevel
          frontier target middleOrder (some handle) scs middleStored fragment fragmentPending separate
        refine ⟨nextLevel, ?_⟩
        rw [core]
        exact EnumerationOrder.stratified_ancestry _ [] nextLevel (frontier + 1) nextOrder
      have finalGrowth : before.core.counter ≤ after.core.counter := by rw [core]; exact growth
      have afterPacket : Packet formulas solver next reached final metadata after := by
        obtain ⟨level, frontier, ordered⟩ := packet.ordered
        obtain ⟨nextLevel, nextOrder⟩ := orders level frontier ordered
        refine ⟨post.context, afterSafe, afterPending,
          ⟨afterRoots, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags⟩,
          ⟨nextLevel, frontier + 1, nextOrder⟩, ?_⟩
        intro group member entry listed
        exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) finalGrowth
      have finalFragmentBound : FragmentBound after.core.counter fragment := by rw [core]; exact fragmentBound
      have finalRoot : IsRoot after.core.representatives target := by rw [core]; exact frame.root
      have ancestry : after.core.expansionAncestry = [] := by rw [core]
      have finalCounter : after.core.counter ≤ before.core.counter + 1 := by rw [core]; exact counterBound
      have finalMass : suspendedBound after.core ≤ suspendedBound before.core + scs.length := by
        have scalars := SourcePruningEnumerationFinalize.run_scalars reached.checked.native.machine.heap
          finalFuel target fragment middle after (by simpa only [Nat.add_zero] using finalRun 0)
        exact Nat.le_trans scalars.2 massBound
      refine ⟨childBound + finalFuel, .complete fragment reached saved after, reached, saved, final, next,
        ?_, post, query, rfl,
        ⟨afterPacket.valid, afterSafe, finalFragmentBound, finalStored, ancestry, finalRoot⟩,
        afterPending, ⟨finalGrowth, finalPending, orders⟩, afterFits, afterKnown,
        Or.inl ⟨fragment, after, rfl, afterPacket, finalCounter, finalMass⟩⟩
      intro extra
      have finished := finalRun (childBound + extra)
      have common : finalFuel + (childBound + extra) = childBound + finalFuel + extra := by omega
      rw [common] at finished
      simp only [SourcePruningEnumerationSelectedOpaqueDispatch.run, ite_eq_right empty,
        childAt (childBound + finalFuel + extra) (by omega), finished, Option.map_some]
      cases value <;> simp_all

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
