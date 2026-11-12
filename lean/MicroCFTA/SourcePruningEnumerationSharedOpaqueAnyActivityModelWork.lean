import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueResources
import MicroCFTA.SourcePruningEnumerationSharedNonterminalChildModels
import MicroCFTA.SourcePruningEnumerationSharedOpaqueAnyActivityWork
import MicroCFTA.SourcePruningEnumerationSharedChildProper
import MicroCFTA.SourcePruningEnumerationOwnFinalizeProper
import MicroCFTA.SourcePruningEnumerationNativeProgress
import MicroCFTA.SourcePruningEnumerationNativeWork
import MicroCFTA.EnumerationCompleteness

/-!
# The model and exact debit of an opaque head

One resource producer fixes the head receipt and complete memo bundle.
The same child installs the selected old term at its fresh parked slot.
The work debit is one for an active target and zero for an inactive target.
The same child and finalizer retain proper storage from a proper input cache.
This law stops before the Left callback and recursive continuation.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationOrigins
open EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "receiptAdvance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- One opaque head retains its model, resource packet and exact target flag debit. -/
theorem opaque_complete_models_resources_work_any_activity
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
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (bounded : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (scs.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (whole : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (old : AssignmentOrigins whole before.core.counter assignment)
    (accepted : InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
      ambient value (assignment target)) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (reached : Caller (bits + 2))
      (saved : Queries) (final : Memos) (next : Inventory),
      ((∀ extra, run checkEmpty
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
        receipt = .rejected caller memos.query before) ∧
      FinalizationAt checkEmpty bound target scs value caller before memos.query receipt) ∧
      ∃ (fragment : Fragments.Fragment Symbol) (after : Cached) (extended : Nat → Term Symbol),
        receipt = .complete fragment reached saved after ∧
        extended = install assignment before.core.counter [assignment target] ∧
        (∀ held < before.core.counter, extended held = assignment held) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended before.core ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient reached.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended after.core ∧
        Fragments.fill extended fragment = assignment target ∧
        Fragments.fill extended fragment = extended target ∧
        AssignmentOrigins whole after.core.counter extended ∧
        (∀ sc ∈ scs, Suspended.Holds extended (assignment target) sc) ∧
        pendingSize after.core extended = pendingSize before.core assignment ∧
        (∀ initialBound, SourcePruningEnumerationNativeWork.work initialBound after extended +
          (if before.expandable target then 1 else 0) =
          SourcePruningEnumerationNativeWork.work initialBound before assignment) ∧
        (EnumerationProgress.ProperState before.core →
          EnumerationProgress.ProperState after.core ∧
          ∀ (NextTyping : Type)
            (stop : Option (SourcePruningRecordTypes.Metadata NextTyping → Nat → Bool))
            (order : SourcePruningRecordTypes.Metadata NextTyping → List Nat → Option Nat)
            (nextMetadata : SourcePruningRecordTypes.Metadata NextTyping),
            SourcePruningEnumerationRestart.decision stop order nextMetadata after ≠ some .stuck) := by
  have dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false := by
    cases value with
    | empty | reference _ | node _ _ _ _ =>
        simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
    | union _ _ _ _ | mu _ _ _ _ => rfl
  have nonempty : value ≠ .empty := by
    intro same
    simp only [same, MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  obtain ⟨bound, receipt, reached, saved, final, next, resource⟩ :=
    opaque_complete_resources seed formulas solver inventory caller memos metadata before checkEmpty
      target handle scs value packet ready stored incoming available closed dispatch bounded reserved known
  refine ⟨bound, receipt, reached, saved, final, next, resource, ?_⟩
  rcases resource with ⟨running, _post, _query, _advance, _admitted, _pending, _history,
    _afterFits, _afterKnown, shape, finalization⟩
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  have coherent := packet.context.ready.semantic.ready.semantic.1.normal.facts.coherent
  obtain ⟨preparedHandle, encoded, decoded⟩ :=
    SourcePruningEnumerationNodes.available_readback caller.checked.native.machine.heap value coherent available closed
  have bucketBound : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have slotModel := EnumerationCompleteness.stored_satisfies
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    assignment before.core satisfied target (.unenumerated (some handle) scs) stored
  simp only [slot, Option.map_some, Fragments.slotSatisfies, List.forall_mem_map] at slotModel
  have inherited : ∀ sc ∈ scs, Suspended.Holds assignment (assignment target) sc := slotModel.2
  obtain ⟨_action, modelFuel, modelAfter, extended, _prepared, _actionRun, modelRun,
    _counter, _aligned, _forest, _modelPaths, _modelStorage, _modelRealized, _modelCounts,
    _modelFlags, _fragmentBound, installed, agree, beforeModel, childModel, extendedHeld,
    filled, origins⟩ :=
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.nonterminal_models_origins
      checkEmpty 0 0 0 0 scs value caller before memos.query roots coherent available closed storage
      realized paths counts flags bucketBound nonterminal (SourceEqualityPCSGuard.holds formulas solver)
      ambient (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment whole (assignment target) satisfied accepted inherited old (old target ready.inside)
  let freshCache := SourcePruningEnumerationSharedOpaqueBucketBoundary.after preparedHandle before
  have modelActual := modelRun 0
  simp only [Nat.add_zero] at modelActual
  have canonicalModel := SourcePruningEnumerationSharedOpaqueBucketBoundary.run_exact
    checkEmpty 0 0 0 0 modelFuel scs value preparedHandle caller before memos.query
    encoded decoded boundary nonterminal
  have modelCache : modelAfter = freshCache :=
    Option.some.inj (congrArg Prod.snd (modelActual.symm.trans canonicalModel))
  have canonicalChild := SourcePruningEnumerationSharedOpaqueBucketBoundary.run_exact
    checkEmpty bound bound bound bound bound scs value preparedHandle caller before memos.query
    encoded decoded boundary nonterminal
  have actual := running 0
  simp only [Nat.add_zero] at actual
  have completedHead : ∃ fragment after, receipt = .complete fragment reached saved after := by
    rcases shape with ⟨fragment, after, completed, _rest⟩ | others
    · exact ⟨fragment, after, completed⟩
    · cases finalized : SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap
          bound target (.hole before.core.counter) freshCache with
      | none =>
          have observed := finalize_stopped checkEmpty bound bound bound bound bound target scs value
            caller caller before freshCache memos.query memos.query (.hole before.core.counter)
            freshCache.core before.core before.waiting nonempty dispatch canonicalChild finalized
          have same := Option.some.inj (actual.symm.trans observed)
          rcases others with ⟨_cache, _outer, _waiting, stopped, _bounds⟩ | rejected
          · have impossible := stopped.symm.trans same
            cases impossible
          · have impossible := rejected.symm.trans same
            cases impossible
      | some finished =>
          have observed := SourcePruningEnumerationSharedSelectedOpaqueDispatch.finalized checkEmpty bound bound bound bound bound target scs value
            caller caller before freshCache finished memos.query memos.query (.hole before.core.counter)
            freshCache.core before.core before.waiting nonempty dispatch canonicalChild finalized
          have same := Option.some.inj (actual.symm.trans observed)
          rcases others with ⟨_cache, _outer, _waiting, stopped, _bounds⟩ | rejected
          · have impossible := stopped.symm.trans same
            cases impossible
          · have impossible := rejected.symm.trans same
            cases impossible
  obtain ⟨fragment, after, completed⟩ := completedHead
  rw [completed] at actual
  obtain ⟨fragmentSame, callerSame, _savedSame, afterCounter, _afterValues, _afterFlags, candidateDrop⟩ :=
    SourcePruningEnumerationSharedOpaqueWork.complete_candidates_any_activity
      checkEmpty bound bound bound bound bound target handle scs value preparedHandle caller before
      memos.query fragment reached saved after stored storage.aligned flags encoded decoded
      boundary nonterminal actual
  rw [completed] at finalization
  obtain ⟨middle, _outer, _waiting, childAt, finishAt, finalMeaning⟩ := finalization
  have resourceChild := childAt 0
  simp only [Nat.add_zero] at resourceChild
  have middleSame : middle = freshCache :=
    Option.some.inj (congrArg Prod.snd (resourceChild.symm.trans canonicalChild))
  have currentChildModel : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient reached.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      extended middle.core := by
    simpa only [callerSame, middleSame, modelCache] using childModel
  have filledHead : Fragments.fill extended fragment = assignment target := by
    rw [fragmentSame]
    exact filled
  have finalModel : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient reached.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      extended after.core := by
    apply (finalMeaning _ _ extended).mpr
    refine ⟨EnumerationFrame.neutralize_satisfies _ _ extended target middle.core currentChildModel, ?_⟩
    rw [filledHead, agree target ready.inside]
  have afterOrigins : AssignmentOrigins whole after.core.counter extended := by
    rw [afterCounter]
    simpa only [modelCache, freshCache, SourcePruningEnumerationSharedOpaqueBucketBoundary.after,
      allocated] using origins
  have fresh : extended before.core.counter = assignment target := by
    rw [installed]
    simp only [install, ↓reduceIte]
  have classified : SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      (.unenumerated (some preparedHandle) []) = some false := by
    simp [SourcePruningEnumerationNativeIndex.candidate, decoded, boundary]
  have allocation : SourcePruningEnumerationCachedChild.allocate caller.checked.native.machine.heap
      (some preparedHandle) before = some (before.core.counter, freshCache) := by
    simp only [SourcePruningEnumerationCachedChild.allocate, classified, Option.map_some,
      Bool.false_eq_true, ↓reduceIte, freshCache, SourcePruningEnumerationSharedOpaqueBucketBoundary.after]
  have finished := finishAt 0
  simp only [Nat.add_zero] at finished
  rw [callerSame, fragmentSame, middleSame] at finished
  have pendingSame := SourcePruningEnumerationStorageProgress.opaque_transfer_pendingSize
    caller.checked.native.machine.heap bound target handle preparedHandle scs before freshCache after
    assignment extended storage.aligned stored agree fresh allocation finished
  refine ⟨fragment, after, extended, completed, installed, agree, beforeModel, finalModel,
    filledHead, ?_, afterOrigins, extendedHeld, pendingSame, ?_, ?_⟩
  · rw [filledHead, agree target ready.inside]
  · intro initialBound
    unfold SourcePruningEnumerationNativeWork.work
    rw [pendingSame]
    omega
  · intro proper
    have bucketProper : EnumerationProgress.ProperValue
        (.unenumerated (some handle) scs : UVarValue Symbol) :=
      proper _ (List.mem_of_getElem? stored)
    have inputs : EnumerationProgress.ProperInputs scs := by
      intro sc member
      exact ⟨(bucketProper sc member).1, (bucketProper sc member).2.1⟩
    have middleProper :=
      SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.successful_proper
        proper inputs resourceChild
    have finalizer : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
        bound target fragment middle = some after := by
      simpa only [Nat.add_zero] using finishAt 0
    have afterProper := SourcePruningEnumerationFinalize.run_proper
      reached.checked.native.machine.heap bound target fragment middle after middleProper finalizer
    rw [completed] at _admitted
    refine ⟨afterProper, ?_⟩
    intro NextTyping stop order nextMetadata
    exact SourcePruningEnumerationRestart.not_stuck_of_proper formulas solver stop order nextMetadata
      reached after _admitted.1 _admitted.2.1 afterProper ambient
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      extended finalModel

end MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
