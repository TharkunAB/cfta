import MicroCFTA.SourcePruningEnumerationPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadCoverage
import MicroCFTA.SourcePruningEnumerationConstructorIteration
import MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadResources
import MicroCFTA.SourcePruningEnumerationSelectedEdgeCoverage
import MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage

/-!
# Progress at the actual prepared finite head

The operational head keeps its original bound and complete resource result.
An original accepting assignment gives the same actual receipt a strict
pending-term decrease and a complete recursive Packet. A comparison at a
common sufficient work index identifies the constructive and actual receipts.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationProgress EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds edgeCost)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationPreparedRecursive (Failure continueWith resume Complete OutcomeResources)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "finiteStep" => SourcePruningEnumerationPreparedReservation.step
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual stable head preserves its resources and derives strict accepted-model progress. -/
theorem head_finite_complete_resources_accepting_progress
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (proper : ProperState before.core)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))
    (parentClosed : free = [])
    (selected : edge ∈ storedEdges) (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ selectedEdge ∈ edgesOf (.node entry rows depth free), selectedEdge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationPreparedReservation.HeadReserved bits recursiveFuel seed capturedMass inherited) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (middleCaller : Caller (bits + 2))
      (saved : Queries) (middleMemos : Memos) (middleInventory : Inventory),
      ((∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some receipt) ∧
      Post formulas solver middleInventory caller middleCaller middleMemos ∧ middleMemos.query = saved ∧
      Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
      HeadCacheBounds before scs (scalar seed.2) (guardWidth seed.1) receipt ∧
      Fits (afterHead seed inherited).2 middleCaller.checked ∧
      Heap (fun guard => guard ∈ (afterHead seed inherited).1) middleCaller.checked.native.machine.heap ∧
      ((receipt = .unhandled ∧ arityAllows edge.children.length scs = true ∧
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) ∨
        ∃ outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2),
          advance receipt = some (middleCaller, middleMemos.query) ∧
          (∀ extra, match (generalizing := false) receipt with
            | .complete fragment actual queries after =>
                continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
                  graph templates stop order (bound + extra) metadata uv fragment actual queries after = outcome
            | _ => outcome = .complete [] middleCaller middleMemos.query) ∧
          OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited) outcome ∧
          match outcome with
          | .complete _ actual queries =>
              ∃ (next : Inventory) (final : Memos),
                Post formulas solver next caller actual final ∧ final.query = queries ∧
                Packet formulas solver next actual final metadata before ∧
                Fits (finiteStep recursiveFuel seed capturedMass inherited).2 actual.checked ∧
                Heap (fun guard => guard ∈ (finiteStep recursiveFuel seed capturedMass inherited).1)
                  actual.checked.native.machine.heap
          | .stopped _ _ _ => True)) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol) (afterCache : Cached),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          receipt = .complete fragment middleCaller saved afterCache ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient middleCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended afterCache.core ∧
          ProperState afterCache.core ∧
          EnumerationStorageProgress.pendingSize afterCache.core extended + 1 ≤
            EnumerationStorageProgress.pendingSize before.core assignment ∧
          ∃ (progressInventory : Inventory) (progressMemos : Memos),
            Post formulas solver progressInventory caller middleCaller progressMemos ∧
            progressMemos.query = saved ∧
            Packet formulas solver progressInventory middleCaller progressMemos metadata afterCache := by
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, resources, _accepting⟩ :=
    head_finite_complete_resources_accepting holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver inventory caller memos before uv handle scs
      parentEntry storedEdges depth free edge packet ready stored parentAvailable parentClosed selected incoming
      bounded known selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, resources, ?_⟩
  intro ambient assignment satisfied accepted
  have inheritedModel : ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
    have model := satisfied.1.2 uv
    simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
      List.forall_mem_map] at model
    exact model.2
  obtain ⟨tries, residual, _terms, projected, _valid, _termShape, _children,
    _length, allowed, _ownEqualities, _residualHolds⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
      parentEntry storedEdges depth free edge scs packet.context parentAvailable selected ambient assignment
      (assignment uv) accepted inheritedModel
  obtain ⟨children, own⟩ := SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet
    seed formulas solver inventory caller memos metadata before packet bounded known
    parentEntry storedEdges depth free parentAvailable edge selected
  have costBound := SourcePruningEnumerationRecursiveReservation.edge_cost_le seed inherited scs
    before.core.counter edge children own inheritedLength
  have actualCost : edgeCost scs before.core.counter edge =
      SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries := by
    simp only [edgeCost, allowed, ↓reduceIte, projected]
  have actualReserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [actualCost] using reserved.edge costBound
  obtain ⟨r, n, p, h, k, fragment, actualCaller, recorded, afterCache, actualSaved, progressMemos,
    progressInventory, _afterRoots, extended, original, capturedRun, afterPacket, afterProper,
    _admitted, _history, _pendingInputs⟩ :=
    SourcePruningEnumerationConstructorIteration.accepted_prepared_constructor_packet
      seed formulas solver inventory caller before checkEmpty parentEntry storedEdges depth free edge scs memos
      metadata packet proper uv handle ready incoming stored parentAvailable parentClosed selected
      ambient assignment (assignment uv) rfl satisfied accepted tries residual projected bounded actualReserved known
  rcases original with ⟨_selectedRun, _finalizeRun, progressPost, progressQueries, agree, originalSatisfied,
    filled, _recordedSatisfied, afterSatisfied, _safe, _canonical, _roots, _storage, _realized,
    _counts, _flags, _fits, _known, decrease⟩
  let padding := r + n + p + h + k
  let work := bound + padding
  have rl : r ≤ work := by dsimp [work, padding]; omega
  have nl : n ≤ work := by dsimp [work, padding]; omega
  have pl : p ≤ work := by dsimp [work, padding]; omega
  have hl : h ≤ work := by dsimp [work, padding]; omega
  have kl : k ≤ work := by dsimp [work, padding]; omega
  have capturedAt := capturedRun (work - r) (work - n) work work (work - k) pl hl
  simp only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] at capturedAt
  have receiptSame : receipt = .complete fragment actualCaller actualSaved afterCache :=
    Option.some.inj ((resources.1 padding).symm.trans capturedAt)
  have reached : advance receipt = some (middleCaller, saved) := by
    rcases resources.2.2.2.2.2.2.2.2.2 with ⟨unsupported, _allowed, _projected⟩ |
      ⟨_outcome, advanced, _callback, _resources, _captured⟩
    · rw [receiptSame] at unsupported
      cases unsupported
    · simpa only [resources.2.2.1] using advanced
  rw [receiptSame] at reached
  change some (actualCaller, actualSaved) = some (middleCaller, saved) at reached
  have sameEndpoint := Option.some.inj reached
  have sameCaller : actualCaller = middleCaller := congrArg Prod.fst sameEndpoint
  have sameQueries : actualSaved = saved := congrArg Prod.snd sameEndpoint
  refine ⟨extended, fragment, afterCache, agree, originalSatisfied, ?_, filled, ?_, afterProper,
    decrease, progressInventory, progressMemos, ?_, ?_, ?_⟩
  · simpa only [sameCaller, sameQueries] using receiptSame
  · simpa only [sameCaller] using afterSatisfied
  · simpa only [sameCaller] using progressPost
  · exact progressQueries.trans sameQueries
  · simpa only [sameCaller] using afterPacket

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
