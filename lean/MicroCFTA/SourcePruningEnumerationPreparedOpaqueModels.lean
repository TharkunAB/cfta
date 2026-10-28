import MicroCFTA.SourcePruningEnumerationPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationPreparedOpaqueFiniteResources
import MicroCFTA.SourcePruningEnumerationChildCoverage
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# Original accepted models at actual prepared opaque and terminal callback entries

The finite resource producer fixes its receipt and callback before all models.
The child coverage producer uses the same original state and resources.
One common diagonal identifies its singleton with the actual finite receipt.
Finalization writes the original captured target with that same fragment.
The observer constructs one assignment extension for the original accepted term.
It does not assert that every completion of a fresh opaque hole is valid.
It does not assert a model after the recursive callback.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed advance)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationPreparedRecursive (Failure continueWith resume Complete OutcomeResources finish)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "FoldResult" => SourcePruningEnumerationNativeContinuations.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "receiptAdvance" => SourcePruningEnumerationNativeBranches.advance
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
local notation "finiteStep" => SourcePruningEnumerationPreparedReservation.step
variable {Typing Key : Type} {bits : Nat}

private theorem finalized_core
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel target : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : Cached)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    after.core = {before.core with
      values := before.core.values.set target (.enumerated fragment)
      expansionAncestry := []} := by
  simp only [SourcePruningEnumerationFinalize.run, Option.bind_eq_some_iff] at observed
  obtain ⟨_old, _stored, written⟩ := observed
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
  subst after
  rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The original accepted term reaches the same fixed opaque or terminal callback entry. -/
theorem opaque_finite_complete_resources_models
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (target handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid target before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationPreparedReservation.HeadReserved bits recursiveFuel seed capturedMass inherited) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (middleCaller : Caller (bits + 2))
      (saved : Queries) (middleMemos : Memos) (middleInventory : Inventory)
      (outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))
      (folded : FoldResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      ((∀ extra, SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        target scs value caller before memos.query = some receipt) ∧
      Post formulas solver middleInventory caller middleCaller middleMemos ∧ middleMemos.query = saved ∧
      receiptAdvance receipt = some (middleCaller, saved) ∧
      Admitted target receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
      Fits (advance seed (scs.length + 1)).2 middleCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (scs.length + 1)).1) middleCaller.checked.native.machine.heap ∧
      ((∃ fragment after, receipt = .complete fragment middleCaller saved after ∧
          Packet formulas solver middleInventory middleCaller middleMemos metadata after ∧
          after.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound after.core ≤ suspendedBound before.core + scs.length) ∨
        (∃ after outer waiting, receipt = .stopped []
          (.ok (some []), middleCaller, saved, outer, waiting) (some after) ∧
          after.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound after.core ≤ suspendedBound before.core + scs.length) ∨
        receipt = .rejected caller memos.query before) ∧
      Fits (afterHead seed inherited).2 middleCaller.checked ∧
      Heap (fun guard => guard ∈ (afterHead seed inherited).1) middleCaller.checked.native.machine.heap ∧
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual queries after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
              graph templates stop order (bound + extra) metadata target fragment actual queries after = outcome
        | _ => outcome = .complete [] middleCaller middleMemos.query) ∧
      (∀ extra, SourcePruningEnumerationReceiptContinuation.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata target) (some receipt) = folded) ∧
      OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited)
        (finish target folded) ∧
      (∀ extra, SourcePruningEnumerationReceiptContinuation.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata target)
        (SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          target scs value caller before memos.query) = folded)) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap) residualMeaning assignment before.core →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient value (assignment target) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol) (after : Cached),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap) residualMeaning extended before.core ∧
          receipt = .complete fragment middleCaller saved after ∧
          Fragments.fill extended fragment = assignment target ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient middleCaller.checked.native.machine.heap) residualMeaning extended after.core := by
  have recursive := SourcePruningEnumerationPreparedRecursive.finite_complete
    (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, outcome, folded, retained⟩ :=
    opaque_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver recursive inventory caller memos before target handle scs value
      packet ready stored incoming available closed dispatch bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  have retainedFacts := retained
  rcases retainedFacts with ⟨headRun, _headPost, _headQuery, advanced, _admitted, _pending,
    _history, _headFits, _headKnown, _shape, _paddedFits, _paddedKnown,
    _callback, _foldRun, _resources, _combinedRun⟩
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  have bucketBound : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have pendingInputs := EnumerationReferences.pending_inputs before.core packet.pending
    target (some handle) scs stored
  have positive : 1 ≤ scalar seed.2 := Nat.le_trans bounded.stored.positive
    (SourceCurrentConstrainedCapTargetForecast.scalar_mass seed.2)
  have pay := Nat.mul_le_mul_right (inherited + guardWidth seed.1 + 1) positive
  simp only [Nat.one_mul] at pay
  have costBound : scs.length + 1 ≤ SourcePruningEnumerationRecursiveReservation.edgeCount seed inherited := by
    unfold SourcePruningEnumerationRecursiveReservation.edgeCount
    omega
  obtain ⟨r, n, p, h, k, raw, childCaller, middle, childSaved, childMemos, childInventory,
    childRoots, outer, waiting, childPacket, childModels⟩ :=
    SourcePruningEnumerationChildCompletion.complete_with_fragments_resources_accepting seed formulas solver
      inventory caller before checkEmpty scs value roots memos packet.context packet.safe paths counts flags
      realized bucketBound pendingInputs available closed bounded (reserved.1.prefix costBound) known
  rcases childPacket with ⟨childRun, _childPost, _childQuery, _growth, _childPaths, _childStorage,
    _childRealized, _childCounts, _childFlags, _origin, protects, _references, _history,
    _childShape, _childFits, _childKnown, _terminalModels⟩
  let childBound := r + n + p + h + k
  have childAt (w : Nat) (large : childBound ≤ w) :
      SourcePruningEnumerationChildDispatch.run checkEmpty w w w w w scs value caller before memos.query =
        ((.ok (some raw), childCaller, childSaved, outer, waiting), some middle) := by
    have rl : r ≤ w := by dsimp only [childBound] at large; omega
    have nl : n ≤ w := by dsimp only [childBound] at large; omega
    have pl : p ≤ w := by dsimp only [childBound] at large; omega
    have hl : h ≤ w := by dsimp only [childBound] at large; omega
    have kl : k ≤ w := by dsimp only [childBound] at large; omega
    have actual := childRun (w - r) (w - n) w w (w - k) pl hl
    simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using actual
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, outcome, folded, retained, ?_⟩
  intro ambient residualMeaning assignment original accepted
  have holds : ∀ sc ∈ scs, Suspended.Holds assignment (assignment target) sc := by
    have model := original.1.2 target
    simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
      List.forall_mem_map] at model
    exact model.2
  obtain ⟨extended, fragment, agree, originalExtended, singleton, filled, childModel⟩ :=
    childModels ambient residualMeaning assignment (assignment target) original accepted holds
  have nonempty : value ≠ .empty := by
    intro empty
    rw [empty, InternedGuardedLanguage.meaning] at accepted
    exact accepted
  have actualChild := childAt (bound + childBound) (by omega)
  rw [singleton] at actualChild
  have actual := headRun childBound
  simp only [SourcePruningEnumerationSelectedOpaqueDispatch.run, ite_eq_right nonempty,
    actualChild] at actual
  have mapped : Option.map
      (fun finished => SourcePruningEnumerationSelectedEdge.Result.complete fragment childCaller childSaved finished)
      (SourcePruningEnumerationFinalize.run childCaller.checked.native.machine.heap (bound + childBound)
        target fragment middle) = some receipt := by
    cases value with
    | node entry rows depth free =>
        simpa only [dispatch, Bool.false_eq_true, ↓reduceIte] using actual
    | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
        simpa only [Bool.false_eq_true, ↓reduceIte] using actual
  obtain ⟨after, finalized, receiptSame⟩ := Option.map_eq_some_iff.mp mapped
  have completed : receipt = .complete fragment childCaller childSaved after := receiptSame.symm
  have sameEndpoint : childCaller = middleCaller ∧ childSaved = saved := by
    have actualAdvance := advanced
    rw [completed] at actualAdvance
    change some (childCaller, childSaved) = some (middleCaller, saved) at actualAdvance
    exact Prod.mk.inj (Option.some.inj actualAdvance)
  have frame := protects target ready.inside ready.root (ready.avoids handle scs stored)
  have middleStored : middle.core.values[target]? = some (.unenumerated (some handle) scs) :=
    frame.value.trans stored
  have core := finalized_core childCaller.checked.native.machine.heap (bound + childBound)
    target fragment middle after finalized
  have selfValue : Fragments.fill extended fragment = extended target :=
    filled.trans (agree target ready.inside).symm
  have afterModel := (SourcePruningEnumerationFinalize.written_semantics middle.core after.core target fragment
    (List.getElem?_eq_some_iff.mp middleStored).1 core
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient childCaller.checked.native.machine.heap) residualMeaning extended).mpr
      ⟨EnumerationFrame.neutralize_satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient childCaller.checked.native.machine.heap)
        residualMeaning extended target middle.core childModel, selfValue⟩
  refine ⟨extended, fragment, after, agree, originalExtended, ?_, filled, ?_⟩
  · simpa only [sameEndpoint.1, sameEndpoint.2] using completed
  · simpa only [sameEndpoint.1] using afterModel

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
