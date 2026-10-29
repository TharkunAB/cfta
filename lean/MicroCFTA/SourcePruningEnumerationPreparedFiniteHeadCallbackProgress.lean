import MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadProgress
import MicroCFTA.SourcePruningEnumerationPreparedFiniteReceiptModels
import MicroCFTA.SourcePruningEnumerationPreparedCallbackCostProgress
import MicroCFTA.SourcePruningEnumerationPolicyOrigins

/-!
# Same-model progress through the actual prepared head callback

The original head fixes its receipt and accepting-model observer.
Original receipt resources derive one callback bound before model selection.
The common work controls both actual actions. Original template policies
preserve the same accepting assignment and strict cost through recording.
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
local notation "Refutes" => @SourcePruningResume.Refutes Symbol
  (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq)
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual head and callback retain the same accepted model, strict cost and full resources. -/
theorem head_finite_complete_resources_accepting_callback_progress
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
            Packet formulas solver progressInventory middleCaller progressMemos metadata afterCache ∧
            ∀ extra,
              (∀ group ∈ metadata.pending, Refutes assignment group) →
              SourcePruningTemplates.Avoids templates (assignment uv) →
              (∀ program, SourcePruningTemplates.ProgramAt (assignment uv) program →
                SourcePruningTemplates.ProgramEncoding program) →
              SourcePruningEnumerationPreparedRecursive.CallbackProgressAt formulas solver progressInventory
                graph templates metadata uv fragment middleCaller progressMemos afterCache ambient extended
                (EnumerationStorageProgress.pendingSize before.core assignment) (bound + extra) := by
  obtain ⟨oldBound, receipt, middleCaller, saved, middleMemos, middleInventory, resources, accepting⟩ :=
    head_finite_complete_resources_accepting_progress holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver inventory caller memos before uv handle scs
      parentEntry storedEdges depth free edge packet proper ready stored parentAvailable parentClosed selected incoming
      bounded known selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved
  rcases resources with ⟨headRun, headPost, headQueries, admitted, pending, history, cacheBounds,
    headFits, headKnown, shape⟩
  rcases shape with unsupported | ⟨outcome, advanced, callbackRun, outcomeResources, captured⟩
  · refine ⟨oldBound, receipt, middleCaller, saved, middleMemos, middleInventory,
      ⟨headRun, headPost, headQueries, admitted, pending, history, cacheBounds,
        headFits, headKnown, .inl unsupported⟩, ?_⟩
    intro ambient assignment satisfied accepted
    obtain ⟨extended, fragment, afterCache, _agree, _original, completed, _filled, _model,
      _proper, _decrease, _progress⟩ := accepting ambient assignment satisfied accepted
    rw [unsupported.1] at completed
    cases completed
  · have mass := SourcePruningEnumerationRecursiveReservation.head_mass_le seed capturedMass inherited
      before scs receipt initialMass inheritedLength cacheBounds
    obtain ⟨modelFuel, _modelOutcome, _modelResources, recording⟩ :=
      SourcePruningEnumerationPreparedRecursive.receipt_finite_complete_resources_models
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver recursiveFuel
        inventory middleInventory caller middleCaller memos middleMemos before uv receipt packet headPost advanced
        admitted pending history (afterHead seed inherited) (massCeil seed capturedMass inherited)
        headFits headKnown selectionMembers selectionLength (by cases receipt <;> exact mass) reserved.2
    let bound := oldBound + modelFuel
    refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory,
      ⟨?_, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown,
        .inr ⟨outcome, advanced, ?_, outcomeResources, captured⟩⟩, ?_⟩
    · intro extra
      simpa only [bound, ←Nat.add_assoc] using headRun (modelFuel + extra)
    · intro extra
      cases receipt <;> simpa only [bound, ←Nat.add_assoc] using callbackRun (modelFuel + extra)
    · intro ambient assignment satisfied accepted
      obtain ⟨extended, fragment, afterCache, agree, originalSatisfied, completed, filled, afterSatisfied,
        afterProper, decrease, progressInventory, progressMemos, progressPost, progressQuery, progressPacket⟩ :=
        accepting ambient assignment satisfied accepted
      refine ⟨extended, fragment, afterCache, agree, originalSatisfied, completed, filled, afterSatisfied,
        afterProper, decrease, progressInventory, progressMemos, progressPost, progressQuery, progressPacket, ?_⟩
      rw [completed] at recording
      obtain ⟨_callerSame, _querySame, recorded, callbackCore, _current, allocated, returned, _equivalence, _models⟩ := recording
      obtain ⟨_callbackPacket, _stable, _frame, _types, _holes, _typing, callback, _running, _resources⟩ := returned
      intro extra refuted avoids encoded
      have common : modelFuel + (oldBound + extra) = bound + extra := by dsimp [bound]; omega
      have observed := (callback (oldBound + extra)).1
      rw [common] at observed
      have extendedRefuted := SourcePruningRecordTypes.pending_refutes_extension
        before.core.counter assignment extended metadata packet.bounded agree refuted
      have filledSelf : Fragments.fill extended fragment = extended uv :=
        filled.trans (agree uv ready.inside).symm
      exact SourcePruningEnumerationPreparedRecursive.callback_progress_at_of_success
        formulas solver progressInventory graph templates metadata uv fragment middleCaller progressMemos afterCache
        (bound + extra) recorded callbackCore progressPacket allocated afterProper observed ambient extended afterSatisfied
        filledSelf extendedRefuted (by simpa only [filled] using avoids) (by simpa only [filled] using encoded)
        (EnumerationStorageProgress.pendingSize before.core assignment) decrease

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
