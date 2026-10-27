import MicroCFTA.SourcePruningEnumerationRecursiveReservation
import MicroCFTA.SourcePruningEnumerationFiniteReceiptResources
import MicroCFTA.SourcePruningEnumerationSubtreeEffects
import MicroCFTA.SourcePruningEnumerationNativeHeadProper

/-!
# Proper storage in the actual finite callback head receipt

The original finite producer and complete callback outcome remain available.
Original proper storage derives the same actual head receipt cache property.
This result makes no claim about an arbitrary callback subtree cache.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds edgeCost)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume Complete OutcomeResources)
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
local notation "finiteStep" => SourcePruningEnumerationFiniteReservation.step
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Keep the entire finite head packet and derive proper storage at its own actual receipt. -/
theorem head_finite_complete_resources_proper
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
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
      (EnumerationProgress.ProperState before.core →
        match (generalizing := false) receipt with
        | .complete _ _ _ after | .rejected _ _ after => EnumerationProgress.ProperState after.core
        | .stopped _ _ (some after) => EnumerationProgress.ProperState after.core
        | _ => True) := by
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory,
    running, post, querySame, admitted, pendingReceipt, history, cacheBounds, returnedFits, returnedKnown, shape⟩ :=
    head_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges depth free edge
      packet ready stored decoded selected incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory,
    ⟨running, post, querySame, admitted, pendingReceipt, history, cacheBounds, returnedFits, returnedKnown, shape⟩, ?_⟩
  intro proper
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  have pending := EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
  exact SourcePruningEnumerationNativeBranchCompletion.observed_cache_proper
    formulas solver inventory caller before checkEmpty uv handle scs parentEntry storedEdges depth free edge roots memos
    packet.context ready stored decoded realized selected paths counts flags pending proper
    (by simpa only [Nat.add_zero] using running 0)

end MicroCFTA.SourcePruningEnumerationNativeHookResources
