import MicroCFTA.SourcePruningEnumerationSharedPreparedBranchWork
import MicroCFTA.SourcePruningEnumerationSharedOpaqueAnyActivityModelWork

/-!
# Ordinary and opaque heads after the same preparation

One prepared producer supplies the common carrier and ordinary result.
The opaque result uses that same carrier and one actual opaque head.
The current incoming-reference condition moves through the actual read.
Ready does not imply the incoming-reference condition.
The opaque work debit uses the original cache before preparation.
This result stops before the Left callback and recursive continuation.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedHeadWork
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

open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory)

/-- One preparation retains its complete ordinary packet and its opaque head packet. -/
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
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
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
      (∀ (entry : Cache.Interned InternedBinderProtocol.NodeKey)
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
        SourcePruningEnumerationRestart.decision stop order nextMetadata after ≠ some .stuck) ∧
      (MergedOrdinaryHeight.recursiveBoundary result = true →
    ∃ (headBound : Nat) (receipt : Result (bits + 2)) (reached : Caller (bits + 2))
      (saved : Queries) (final : Memos) (next : Inventory),
      Post formulas solver next caller reached final ∧
      ((∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (headBound + extra) (headBound + extra) (headBound + extra) (headBound + extra) (headBound + extra)
        uv scs result (advanceCaller caller heap) entered memos.query = some receipt) ∧
      Post formulas solver next (advanceCaller caller heap) reached final ∧ final.query = saved ∧
      SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance receipt = some (reached, saved) ∧
      Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory entered.core receipt ∧
      Fits (advance (preparedSeed seed) (scs.length + 1)).2 reached.checked ∧
      Heap (fun guard => guard ∈ (advance (preparedSeed seed) (scs.length + 1)).1) reached.checked.native.machine.heap ∧
      ((∃ fragment after, receipt = .complete fragment reached saved after ∧
          Packet formulas solver next reached final metadata after ∧
          after.core.counter ≤ entered.core.counter + 1 ∧
          SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core + scs.length) ∨
        (∃ after outer waiting, receipt = .stopped []
          (.ok (some []), reached, saved, outer, waiting) (some after) ∧
          after.core.counter ≤ entered.core.counter + 1 ∧
          SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core + scs.length) ∨
        receipt = .rejected (advanceCaller caller heap) memos.query entered) ∧
      SourcePruningEnumerationSharedSelectedOpaqueDispatch.FinalizationAt checkEmpty headBound uv scs result (advanceCaller caller heap) entered memos.query receipt) ∧
      ∃ (fragment : Fragments.Fragment Symbol) (after : Cached) (extended : Nat → Term Symbol),
        (receipt = .complete fragment reached saved after ∧
        extended = install assignment entered.core.counter [assignment uv] ∧
        (∀ held < entered.core.counter, extended held = assignment held) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient (advanceCaller caller heap).checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended entered.core ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient reached.checked.native.machine.heap)
          (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
          extended after.core ∧
        Fragments.fill extended fragment = assignment uv ∧
        Fragments.fill extended fragment = extended uv ∧
        AssignmentOrigins whole after.core.counter extended ∧
        (∀ sc ∈ scs, Suspended.Holds extended (assignment uv) sc) ∧
        EnumerationStorageProgress.pendingSize after.core extended = EnumerationStorageProgress.pendingSize entered.core assignment ∧
        (∀ headInitialBound, SourcePruningEnumerationNativeWork.work headInitialBound after extended +
          (if entered.expandable uv then 1 else 0) =
          SourcePruningEnumerationNativeWork.work headInitialBound entered assignment) ∧
        (EnumerationProgress.ProperState entered.core →
          EnumerationProgress.ProperState after.core ∧
          ∀ (NextTyping : Type)
            (stop : Option (SourcePruningRecordTypes.Metadata NextTyping → Nat → Bool))
            (order : SourcePruningRecordTypes.Metadata NextTyping → List Nat → Option Nat)
            (nextMetadata : SourcePruningRecordTypes.Metadata NextTyping),
            SourcePruningEnumerationRestart.decision stop order nextMetadata after ≠ some .stuck)) ∧
        EnumerationStorageProgress.pendingSize after.core extended =
          EnumerationStorageProgress.pendingSize before.core assignment ∧
        SourcePruningEnumerationNativeWork.work initialBound after extended +
          (if before.expandable uv then 1 else 0) =
          SourcePruningEnumerationNativeWork.work initialBound before assignment ∧
        EnumerationProgress.ProperState after.core ∧
        ∀ (NextTyping : Type)
          (stop : Option (SourcePruningRecordTypes.Metadata NextTyping → Nat → Bool))
          (order : SourcePruningRecordTypes.Metadata NextTyping → List Nat → Option Nat)
          (nextMetadata : SourcePruningRecordTypes.Metadata NextTyping),
          SourcePruningEnumerationRestart.decision stop order nextMetadata after ≠ some .stuck) := by
  obtain ⟨bound, decoded, result, heap, entered, preparation,
    enteredModel, enteredOrigins, accepted, ordinary⟩ :=
    SourcePruningEnumerationSharedPreparedBranchModels.complete_models_resources_work_proper_progress
      seed formulas solver inventory caller memos metadata before uv handle scs checkEmpty
      packet ready stored bounded known ceiling inheritedLength reserved ambient assignment whole
      satisfied old proper initialBound currentBound
  refine ⟨bound, decoded, result, heap, entered, preparation,
    enteredModel, enteredOrigins, accepted, ordinary, ?_⟩
  intro boundary
  have retained := preparation.1
  rcases retained with ⟨_running, _lookup, preparationPost, enteredPacket, stable,
    enteredReady, enteredStored, counter, valuesSame, flagsSame, _waiting,
    available, closed, _meaning, _satisfaction⟩
  have enteredProper : EnumerationProgress.ProperState entered.core := by
    intro value member
    rw [valuesSame] at member
    exact proper value member
  have payload : EnumerationProgress.ProperValue
      (.unenumerated (some handle) scs : UVarValue Symbol) :=
    proper _ (List.mem_of_getElem? stored)
  have nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
    exact List.any_eq_false.mpr (fun sc member => by
      simp only [(payload sc member).2.2, Bool.false_eq_true, not_false_eq_true])
  have enteredIncoming : EnumerationReferences.IncomingAvoid uv entered.core :=
    EnumerationReferences.incoming_read uv before.core entered.core stable incoming
  have enteredPending : EnumerationStorageProgress.pendingSize entered.core assignment =
      EnumerationStorageProgress.pendingSize before.core assignment := by
    unfold EnumerationStorageProgress.pendingSize
    rw [valuesSame]
  have enteredWork : SourcePruningEnumerationNativeWork.work initialBound entered assignment =
      SourcePruningEnumerationNativeWork.work initialBound before assignment := by
    unfold SourcePruningEnumerationNativeWork.work
    rw [enteredPending]
    simp only [EnumerationIndexSelection.candidates, counter, flagsSame]
  have currentFits : Fits (preparedSeed seed).2 (advanceCaller caller heap).checked := preparation.2.1
  have currentKnown : Heap (fun guard => guard ∈ (preparedSeed seed).1)
      (advanceCaller caller heap).checked.native.machine.heap := preparation.2.2.2
  have positive : 1 ≤ SourceCurrentConstrainedCapTargetForecast.scalar (preparedSeed seed).2 :=
    Nat.le_trans currentFits.stored.positive
      (SourceCurrentConstrainedCapTargetForecast.scalar_mass (preparedSeed seed).2)
  have pay := Nat.mul_le_mul_right
    (ceiling + SourcePruningEnumerationGuardWidth.width (preparedSeed seed).1 + 1) positive
  simp only [Nat.one_mul] at pay
  have costBound : scs.length + 1 ≤
      SourcePruningEnumerationRecursiveReservation.edgeCount (preparedSeed seed) ceiling := by
    unfold SourcePruningEnumerationRecursiveReservation.edgeCount
    omega
  have headReserved : SourcePruningEnumerationSharedIncomingReservation.Reserved bits
      (preparedSeed seed) (scs.length + 1) :=
    SourcePruningEnumerationSharedPreparedReservation.HeadReserved.edge
      (SourcePruningEnumerationSharedPreparedReservation.Reserved.first reserved) costBound
  obtain ⟨headBound, receipt, reached, saved, final, next, resource,
    fragment, after, extended, completed, installed, agree, inputModel, outputModel,
    filledOriginal, filled, origins, inherited, pendingSame, workSame, progress⟩ :=
    SourcePruningEnumerationSharedSelectedOpaqueDispatch.opaque_complete_models_resources_work_any_activity
      (preparedSeed seed) formulas solver inventory (advanceCaller caller heap) memos metadata
      entered checkEmpty uv handle scs result enteredPacket enteredReady enteredStored enteredIncoming
      available closed boundary nonterminal currentFits headReserved currentKnown ambient
      assignment whole enteredModel enteredOrigins accepted
  have models := And.intro completed (And.intro installed (And.intro agree
    (And.intro inputModel (And.intro outputModel (And.intro filledOriginal (And.intro filled
      (And.intro origins (And.intro inherited (And.intro pendingSame (And.intro workSame progress))))))))))
  obtain ⟨afterProper, notStuck⟩ := progress enteredProper
  refine ⟨headBound, receipt, reached, saved, final, next,
    preparationPost.trans resource.2.1, resource, fragment, after, extended, models, ?_, ?_, afterProper, notStuck⟩
  · exact pendingSame.trans enteredPending
  · have debit := workSame initialBound
    rw [flagsSame, enteredWork] at debit
    exact debit

end MicroCFTA.SourcePruningEnumerationSharedPreparedHeadWork
