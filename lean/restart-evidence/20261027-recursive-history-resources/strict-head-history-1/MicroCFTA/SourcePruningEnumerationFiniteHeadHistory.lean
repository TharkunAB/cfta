import MicroCFTA.SourcePruningEnumerationFiniteCallbackHistory
import MicroCFTA.SourcePruningEnumerationCallbackAdmission

/-!
# Actual native heads with admitted smaller-depth output histories

The original head producer supplies its same stable receipt and full memos.
A completed head admits the concrete callback at that exact returned cache.
One common bound covers the head, callback and every returned history.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds edgeCost)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume CompleteWithHistory OutcomeResources)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "finiteStep" => SourcePruningEnumerationFiniteReservation.step
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

variable [DecidableEq Symbol] [DecidableEq Node]

local notation "CallbackResult" => HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- Retain the whole head packet and append actual false-callback output histories. -/
theorem head_finite_complete_resources_with_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selected : edge ∈ storedEdges) (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ selectedEdge ∈ edgesOf (.node entry rows depth free), selectedEdge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationFiniteReservation.HeadReserved bits recursiveFuel seed capturedMass inherited) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (middleCaller : Caller (bits + 2))
      (saved : Queries) (middleMemos : Memos) (middleInventory : Inventory),
      (∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty
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
          (match outcome with
          | .complete _ actual queries =>
              ∃ (next : Inventory) (final : Memos),
                Post formulas solver next caller actual final ∧ final.query = queries ∧
                Packet formulas solver next actual final metadata before ∧
                Fits (finiteStep recursiveFuel seed capturedMass inherited).2 actual.checked ∧
                Heap (fun guard => guard ∈ (finiteStep recursiveFuel seed capturedMass inherited).1)
                  actual.checked.native.machine.heap
          | .stopped _ _ _ => True) ∧
          (match (generalizing := false) receipt with
          | .complete fragment actual queries after =>
              ∃ (result : Bool × SourcePruningRecordTypes.Metadata Typing) (callbackCore : Core),
                (∀ extra,
                  Success (SourcePruningRecordTypes.recordTypes graph templates (bound + extra) metadata uv
                    (.inl fragment)) after.core result callbackCore ∧
                  ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (bound + extra) metadata uv
                    (.inl fragment) after.core) = [.ok (result, callbackCore)] ∧
                  ∀ (recur : SourcePruningRecordTypes.Metadata Typing → Caller (bits + 2) → Queries → Cached →
                    Option Next → CallbackResult) stop order,
                    continueWith recur graph templates stop order (bound + extra) metadata uv fragment actual
                      middleMemos.query after =
                      if result.1 then .complete [] actual middleMemos.query
                      else recur result.2 actual middleMemos.query (EnumerationExpandableIndex.frame callbackCore after)
                        (SourcePruningEnumerationRestart.decision stop order result.2
                          (EnumerationExpandableIndex.frame callbackCore after))) ∧
                SourcePruningEnumerationRecursive.RecursiveCallbackAdmission formulas solver middleInventory
                  actual middleMemos result.2 (EnumerationExpandableIndex.frame callbackCore after)
                  uv fragment recursiveFuel (afterHead seed inherited) (massCeil seed capturedMass inherited) ∧
                (∀ extra, result.1 = false →
                  ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
                    SourcePruningEnumerationRecursive.ResourceHistory holeKey fits admits graph templates checkEmpty
                      edgesOf stop order formulas solver (bound + extra) recursiveFuel middleInventory actual middleMemos
                      result.2 (EnumerationExpandableIndex.frame callbackCore after)
                      (afterHead seed inherited) (massCeil seed capturedMass inherited)
                      (SourcePruningEnumerationRestart.decision stop order result.2
                        (EnumerationExpandableIndex.frame callbackCore after)) output)
          | _ => True)) ∧
      (∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached),
        receipt = .complete fragment reached queries after →
        CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before checkEmpty uv scs edge
          bound fragment reached queries after middleInventory middleMemos) ∧
      ∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached),
        receipt = .complete fragment reached queries after →
        SourcePruningEnumerationRecursive.RecursiveCallbackAdmission formulas solver middleInventory reached middleMemos
          metadata after uv fragment recursiveFuel (afterHead seed inherited) (massCeil seed capturedMass inherited) := by
  obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
    headRun, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
    shape, completedReceipt, callbackAdmission⟩ :=
    head_finite_complete_resources_with_callback_admission holeKey fits admits graph templates checkEmpty edgesOf
      stop order metadata recursiveFuel seed formulas solver recursive.forget inventory caller memos before uv handle scs
      parentEntry storedEdges depth free edge packet ready stored decoded selected incoming bounded known selectionMembers
      selectionLength capturedMass inherited initialMass inheritedLength reserved
  rcases shape with unsupported | ⟨outcome, advanced, callbackRun, resources, captured⟩
  · exact ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
      headRun, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
      .inl unsupported, completedReceipt, callbackAdmission⟩
  · cases receipt with
    | unhandled => cases advanced
    | rejected actual queries after =>
        exact ⟨headBound, .rejected actual queries after, middleCaller, saved, middleMemos, middleInventory,
          headRun, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
          .inr ⟨outcome, advanced, callbackRun, resources, captured, trivial⟩, completedReceipt, callbackAdmission⟩
    | stopped fragments observation candidate =>
        exact ⟨headBound, .stopped fragments observation candidate, middleCaller, saved, middleMemos, middleInventory,
          headRun, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
          .inr ⟨outcome, advanced, callbackRun, resources, captured, trivial⟩, completedReceipt, callbackAdmission⟩
    | complete fragment actual queries after =>
        have actualReceipt := completedReceipt fragment actual queries after rfl
        have admission := callbackAdmission fragment actual queries after rfl
        obtain ⟨callbackFuel, result, callbackCore, callbackOutcome,
          _returned, _stable, _frame, _types, _holes, _typing, callback, richRun,
          _richResources, returnedAdmission, histories⟩ :=
          SourcePruningEnumerationRecursive.callback_finite_complete_resources_with_history
            holeKey fits admits formulas solver middleInventory graph templates metadata uv fragment actual middleMemos after
            checkEmpty edgesOf stop order recursiveFuel recursive (afterHead seed inherited)
            (massCeil seed capturedMass inherited) admission.packet admission.allocated admission.bounded admission.known
            selectionMembers selectionLength admission.mass admission.reserved
        have outcomeSame : outcome = callbackOutcome := by
          have first := callbackRun callbackFuel
          have second := richRun headBound
          rw [Nat.add_comm callbackFuel headBound, actualReceipt.query] at second
          exact first.symm.trans second
        subst callbackOutcome
        refine ⟨headBound + callbackFuel, .complete fragment actual queries after,
          middleCaller, saved, middleMemos, middleInventory,
          ?_, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown,
          .inr ⟨outcome, advanced, ?_, resources, captured, ?_⟩, ?_, callbackAdmission⟩
        · intro extra
          simpa only [Nat.add_assoc] using headRun (callbackFuel + extra)
        · intro extra
          simpa only [Nat.add_assoc] using callbackRun (callbackFuel + extra)
        · refine ⟨result, callbackCore, ?_, returnedAdmission, ?_⟩
          · intro extra
            have actualCallback := callback (headBound + extra)
            have common : callbackFuel + (headBound + extra) = headBound + callbackFuel + extra := by omega
            rw [common] at actualCallback
            exact actualCallback
          · intro extra accepted output member
            have actualHistory := histories (headBound + extra) accepted output member
            have common : callbackFuel + (headBound + extra) = headBound + callbackFuel + extra := by omega
            rw [common] at actualHistory
            exact actualHistory
        · intro nextFragment nextCaller nextQueries nextCache completed
          have certificate := completedReceipt nextFragment nextCaller nextQueries nextCache completed
          exact { certificate with running := fun extra => by
            simpa only [Nat.add_assoc] using certificate.running (callbackFuel + extra) }

end MicroCFTA.SourcePruningEnumerationNativeHookResources
