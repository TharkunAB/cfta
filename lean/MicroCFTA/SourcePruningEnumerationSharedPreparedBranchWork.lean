import MicroCFTA.SourcePruningEnumerationSharedCapturedProgressWork
import MicroCFTA.SourcePruningEnumerationSelectedPreparationCarrier
import MicroCFTA.SourcePruningEnumerationSharedPreparedReservation
import MicroCFTA.SourcePruningEnumerationSharedRecursiveReservationBounds
import MicroCFTA.SourcePruningEnumerationSelectorLanguage

/-!
# Work and local progress after one actual common preparation

The preparation retains the current values and their proper paths.
The stored slot then has no terminal constraint.
One captured producer returns the same resource packet and finite model.
Its returned cache decreases work and has proper paths and local progress.
The ordinary result remains conditional on its literal node shape.
This result does not derive a policy prefix or a chosen scheduler decision.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedBranchModels
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationSharedPreparedReservation (preparedSeed)
open SourcePruningEnumerationSharedRecursiveReservation (narrowSeed)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationOrigins
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "advanceCaller" => SourcePruningEnumerationSelectedValueCaller.advance
local notation "advance" => SourcePruningEnumerationSharedIncomingReservation.advance
local notation "run" => SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run
attribute [local irreducible] SourcePruningEnumerationSharedPreparedReservation.step
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- One prepared branch retains work decrease and local progress at the same witness. -/
theorem complete_models_resources_work_proper_progress
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (before : Cached)
    (uv handle : Nat) (scs : List Suspended) (checkEmpty : Bool)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (bounded : Fits (narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ceiling : Nat) (inheritedLength : scs.length ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits 1 seed ceiling)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Term Symbol) (whole : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core)
    (old : AssignmentOrigins whole before.core.counter assignment)
    (proper : EnumerationProgress.ProperState before.core)
    (initialBound : Nat)
    (currentBound : EnumerationStorageProgress.pendingSize before.core assignment ≤ initialBound) :
    ∃ (bound : Nat) (decoded result : Node) (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
      (((∀ extra, SourcePruningEnumerationSelectedPreparation.run (bound + extra) (bound + extra) uv caller before =
        ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap))) ∧
      lookupNode caller.checked.native.machine.heap handle = some decoded ∧
      Post formulas solver inventory caller
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos ∧
      Packet formulas solver inventory
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos metadata entered ∧
      EnumerationDriver.RenderStable before.core entered.core ∧
      EnumerationDriver.Ready uv entered.core ∧
      entered.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      entered.core.counter = before.core.counter ∧ entered.core.values = before.core.values ∧
      entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
      Available heap result ∧ result.free = [] ∧
      (∀ holds ambient term,
        InternedGuardedLanguage.meaning holds ambient result term ↔
          InternedGuardedLanguage.meaning holds ambient decoded term) ∧
      ∀ holds ambient residualMeaning assignment,
        (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
          residualMeaning assignment entered.core ↔
        Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
          caller.checked.native.machine.heap) residualMeaning assignment before.core) ∧
        (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
          caller.checked.native.machine.heap) residualMeaning assignment before.core →
          InternedGuardedLanguage.meaning holds ambient result (assignment uv))) ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile (narrowSeed seed).2)
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap).checked ∧
      InternedValueMass.value result ≤
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile (narrowSeed seed).2).mass ∧
      InternedFreshOrdinaryConstraintHeap.Heap (fun guard => guard ∈ seed.1) heap) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
        assignment entered.core ∧
      AssignmentOrigins whole entered.core.counter assignment ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient result (assignment uv) ∧
      ∀ (entry : Cache.Interned InternedBinderProtocol.NodeKey)
        (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)
        (free : List InternedBinderProtocol.Reference), result = .node entry rows depth free →
        scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
        ∃ (edge : EdgeValue Symbol Constraint),
          edge ∈ SourceCurrentEnumerationOrder.internedEdgesOf InternedEdgeResidency.nodeEdges
            decoded (.node entry rows depth free) ∧ edge ∈ rows ∧
          InternedEdgeResidency.EdgeResident heap edge ∧
          InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient edge (assignment uv) ∧
        ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
          ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result (bits + 2)),
      (Post formulas solver next caller afterCaller final ∧
      ((∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge (advanceCaller caller heap) entered memos.query = some result) ∧
      Post formulas solver next (advanceCaller caller heap) afterCaller final ∧ final.query = savedQueries ∧
      entered.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (∀ held fragment, held ≠ uv → after.core.values[held]? = some (.enumerated fragment) →
        entered.core.values[held]? = some (.enumerated fragment)) ∧
      InputsPending after.core scs ∧
      (∀ held, held ≠ uv → held < entered.core.counter → IsRoot entered.core.representatives held →
        Avoids entered.core.representatives held scs → EnumerationDriver.Protected held entered.core after.core) ∧
      (EnumerationReferences.PendingReferences entered.core → EnumerationReferences.IncomingAvoid uv entered.core →
        EnumerationReferences.PendingReferences after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧
          after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
          IsRoot after.core.representatives uv ∧ PendingFragment after.core fragment ∧
          ∀ level frontier, EnumerationOrder.Stratified entered.core level frontier →
            ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1)) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance (preparedSeed seed) (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs entered.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance (preparedSeed seed)
        (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs entered.core.counter tries)).1)
        afterCaller.checked.native.machine.heap) ∧
      ∃ (fragment : Fragment) (extended : Nat → Term Symbol),
        result = .complete fragment afterCaller savedQueries after ∧
        (∀ held < entered.core.counter, extended held = assignment held) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient (advanceCaller caller heap).checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended entered.core ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended after.core ∧
        Fragments.fill extended fragment = assignment uv ∧
        Fragments.fill extended fragment = extended uv ∧
        AssignmentOrigins whole after.core.counter extended ∧
        (∀ sc ∈ scs, Suspended.Holds extended (assignment uv) sc) ∧
        EnumerationStorageProgress.pendingSize after.core extended + 1 ≤
          EnumerationStorageProgress.pendingSize before.core assignment ∧
        SourcePruningEnumerationNativeWork.work initialBound after extended <
          SourcePruningEnumerationNativeWork.work initialBound before assignment) ∧
      EnumerationProgress.ProperState after.core ∧
      ∀ (NextTyping : Type)
        (stop : Option (SourcePruningRecordTypes.Metadata NextTyping → Nat → Bool))
        (order : SourcePruningRecordTypes.Metadata NextTyping → List Nat → Option Nat)
        (nextMetadata : SourcePruningRecordTypes.Metadata NextTyping),
        SourcePruningEnumerationRestart.decision stop order nextMetadata after ≠ some .stuck := by
  have payload : EnumerationProgress.ProperValue
      (.unenumerated (some handle) scs : UVarValue Symbol) :=
    proper _ (List.mem_of_getElem? stored)
  have nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
    exact List.any_eq_false.mpr (fun sc member => by
      simp only [(payload sc member).2.2, Bool.false_eq_true, not_false_eq_true])
  obtain ⟨bound, decoded, result, heap, entered, retained, numeric, massBound, knownAfter⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete_resources_carrier
      formulas solver inventory caller memos metadata before uv handle scs packet ready stored
      (narrowSeed seed).2 bounded (fun guard => guard ∈ seed.1) known
  have preparation := retained
  rcases retained with ⟨_running, _decodedLookup, preparationPost, enteredPacket, _stable,
    enteredReady, enteredStored, counter, valuesSame, sameFlags, _sameWaiting, available, closed,
    _meaning, satisfaction⟩
  have enteredProper : EnumerationProgress.ProperState entered.core := by
    intro value member
    rw [valuesSame] at member
    exact proper value member
  have enteredPending : EnumerationStorageProgress.pendingSize entered.core assignment =
      EnumerationStorageProgress.pendingSize before.core assignment := by
    unfold EnumerationStorageProgress.pendingSize
    rw [valuesSame]
  have enteredWork : SourcePruningEnumerationNativeWork.work initialBound entered assignment =
      SourcePruningEnumerationNativeWork.work initialBound before assignment := by
    unfold SourcePruningEnumerationNativeWork.work
    rw [enteredPending]
    simp only [EnumerationIndexSelection.candidates, counter, sameFlags]
  have enteredBound : EnumerationStorageProgress.pendingSize entered.core assignment ≤ initialBound := by
    rw [enteredPending]
    exact currentBound
  have semantic := satisfaction (SourceEqualityPCSGuard.holds formulas solver) ambient
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) assignment
  have enteredModel := semantic.1.mpr satisfied
  have accepted := semantic.2 satisfied
  have enteredOrigins : AssignmentOrigins whole entered.core.counter assignment := by
    rw [counter]
    exact old
  refine ⟨bound, decoded, result, heap, entered,
    ⟨preparation, numeric, massBound, knownAfter⟩, enteredModel, enteredOrigins, accepted, ?_⟩
  intro entry rows depth free ordinary
  subst result
  refine ⟨nonterminal, ?_⟩
  obtain ⟨edge, rawMember, selected, resident, edgeAccepted⟩ :=
    SourcePruningEnumerationSelectorLanguage.interned_accepting heap
      enteredPacket.context.ready.semantic.ready decoded entry rows depth free available
      (SourceEqualityPCSGuard.holds formulas solver) ambient (assignment uv) accepted
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := enteredPacket.valid
  have currentFits : Fits (preparedSeed seed).2 (advanceCaller caller heap).checked := numeric
  have currentKnown : Heap (fun guard => guard ∈ (preparedSeed seed).1)
      (advanceCaller caller heap).checked.native.machine.heap := knownAfter
  have currentAvailable : Available (advanceCaller caller heap).checked.native.machine.heap
      (.node entry rows depth free) := available
  have pending := EnumerationReferences.pending_inputs entered.core enteredPacket.pending
    uv (some handle) scs enteredStored
  have slotModel := EnumerationCompleteness.stored_satisfies
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient heap)
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    assignment entered.core enteredModel uv (.unenumerated (some handle) scs) enteredStored
  simp only [slot, Option.map_some, Fragments.slotSatisfies, List.forall_mem_map] at slotModel
  obtain ⟨tries, residual, _terms, projected, _valid, _shape, _children, _length,
    allowed, _ownEqualities, _residualHeld⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory
      (advanceCaller caller heap) memos entry rows depth free edge scs enteredPacket.context
      currentAvailable selected ambient assignment (assignment uv) edgeAccepted slotModel.2
  obtain ⟨childrenBound, ownBound⟩ :=
    SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet
      (preparedSeed seed) formulas solver inventory (advanceCaller caller heap) memos metadata
      entered enteredPacket currentFits currentKnown entry rows depth free currentAvailable edge selected
  have costBound := SourcePruningEnumerationSharedRecursiveReservation.edge_cost_le
    (preparedSeed seed) ceiling scs entered.core.counter edge childrenBound ownBound inheritedLength
  have exactCost : SourcePruningEnumerationSharedNativeBranchCompletion.edgeCost scs entered.core.counter edge =
      SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs entered.core.counter tries := by
    simp only [SourcePruningEnumerationSharedNativeBranchCompletion.edgeCost, allowed, ↓reduceIte, projected]
  have edgeReserved : SourcePruningEnumerationSharedIncomingReservation.Reserved bits (preparedSeed seed)
      (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs entered.core.counter tries) := by
    rw [← exactCost]
    exact SourcePruningEnumerationSharedPreparedReservation.HeadReserved.edge
      (SourcePruningEnumerationSharedPreparedReservation.Reserved.first reserved) costBound
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    capturedResult, coupled, afterProper, notStuck⟩ :=
    SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.complete_models_resources_work_proper_progress_prepared
      (preparedSeed seed) formulas solver inventory (advanceCaller caller heap) entered checkEmpty
      uv handle scs entry rows depth free edge roots memos enteredPacket.context enteredReady enteredStored
      currentAvailable closed realized selected paths counts flags pending tries residual projected
      currentFits edgeReserved currentKnown ambient assignment whole enteredModel edgeAccepted enteredOrigins initialBound enteredBound enteredProper
  rcases coupled with ⟨resource, models⟩
  rcases models with ⟨fragment, extended, completed, agree, inputModel, outputModel,
    filledOriginal, filled, origins, inherited, decreased, workDecreased⟩
  rw [enteredPending] at decreased
  rw [enteredWork] at workDecreased
  have returnedModels := And.intro completed
    (And.intro agree (And.intro inputModel (And.intro outputModel
      (And.intro filledOriginal (And.intro filled (And.intro origins
        (And.intro inherited (And.intro decreased workDecreased))))))))
  refine ⟨edge, rawMember, selected, resident, edgeAccepted, tries, residual, projected,
    r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    capturedResult, ⟨preparationPost.trans resource.2.1, resource, ⟨fragment, extended, returnedModels⟩⟩, afterProper, notStuck⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedBranchModels
