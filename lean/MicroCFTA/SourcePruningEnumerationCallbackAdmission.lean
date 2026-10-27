import MicroCFTA.SourcePruningEnumerationHeadAdmission
import MicroCFTA.SourcePruningEnumerationFiniteCallbackReceiptLanguage

/-!
# Original resource admission at an actual completed callback input

A completed head retains the planned callback seed and mass ceiling.
The original reservation supplies the smaller-depth callback reservation.
An actual false callback retains this admission at its returned frame.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing : Type} {bits : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]

/-- The actual callback input retains its original finite resource admission. -/
structure RecursiveCallbackAdmission
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (uv : Nat) (fragment : Fragments.Fragment Symbol) (recursiveFuel : Nat) (seed : Seed) (ceiling : Nat) : Prop where
  /-- The callback uses this actual native caller, full memo state and cache. -/
  packet : Packet formulas solver inventory caller memos metadata before
  /-- Every fragment hole names an allocated input variable. -/
  allocated : FragmentBound before.core.counter fragment
  /-- The actual native caller fits the planned callback profile. -/
  bounded : Fits seed.2 caller.checked
  /-- Every current native guard belongs to the planned callback carrier. -/
  known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap
  /-- The actual input cache fits the original mass ceiling. -/
  mass : suspendedBound before.core ≤ ceiling
  /-- The original reservation pays the smaller-depth recursive callback. -/
  reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling

variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq Node]

/-- An actual false callback retains the same seed, mass ceiling and reservation. -/
theorem RecursiveCallbackAdmission.after_false
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {metadata : Metadata Typing} {uv : Nat} {fragment : Fragments.Fragment Symbol}
    {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
    {checkEmpty : Bool} {edgesOf : Node → List (InternedConstructorTemplates.EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {recursiveFuel fuel : Nat} {updated : Metadata Typing} {after : Core}
    {outcome : SourcePruningEnumerationNativeContinuations.HookResult
      (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)}
    {seed : Seed} {ceiling : Nat}
    (admission : RecursiveCallbackAdmission formulas solver inventory caller memos metadata before uv fragment
      recursiveFuel seed ceiling)
    (receipt : FalseCallbackReceipt holeKey fits admits formulas solver inventory graph templates metadata uv fragment
      caller memos before checkEmpty edgesOf stop order recursiveFuel fuel updated after outcome) :
    RecursiveCallbackAdmission formulas solver inventory caller memos updated
      (EnumerationExpandableIndex.frame after before) uv fragment recursiveFuel seed ceiling := by
  refine ⟨receipt.returned, ?_, admission.bounded, admission.known, ?_, admission.reserved⟩
  · change FragmentBound after.counter fragment
    rw [receipt.frame.counter]
    exact admission.allocated
  · change suspendedBound after ≤ ceiling
    rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after receipt.frame.values]
    exact admission.mass

end MicroCFTA.SourcePruningEnumerationRecursive

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
variable [DecidableEq (EdgeKey Symbol Constraint)]

variable [DecidableEq Symbol] [DecidableEq Node]

/-- Keep the full actual head packet and append the original callback resource admission. -/
theorem head_finite_complete_resources_with_callback_admission
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
          match outcome with
          | .complete _ actual queries =>
              ∃ (next : Inventory) (final : Memos),
                Post formulas solver next caller actual final ∧ final.query = queries ∧
                Packet formulas solver next actual final metadata before ∧
                Fits (finiteStep recursiveFuel seed capturedMass inherited).2 actual.checked ∧
                Heap (fun guard => guard ∈ (finiteStep recursiveFuel seed capturedMass inherited).1)
                  actual.checked.native.machine.heap
          | .stopped _ _ _ => True) ∧
      (∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached),
        receipt = .complete fragment reached queries after →
        CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before checkEmpty uv scs edge
          bound fragment reached queries after middleInventory middleMemos) ∧
      ∀ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached),
        receipt = .complete fragment reached queries after →
        SourcePruningEnumerationRecursive.RecursiveCallbackAdmission formulas solver middleInventory reached middleMemos
          metadata after uv fragment recursiveFuel (afterHead seed inherited) (massCeil seed capturedMass inherited) := by
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory,
    running, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown, shape, completedReceipt⟩ :=
    head_finite_complete_resources_with_receipt holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges
      depth free edge packet ready stored decoded selected incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory,
    running, post, querySame, admitted, pending, history, cacheBounds, headFits, headKnown, shape, completedReceipt, ?_⟩
  intro fragment reached queries after completed
  have actualReceipt := completedReceipt fragment reached queries after completed
  have actualAdmitted : Admitted uv (.complete fragment reached queries after) := by
    simpa only [completed] using admitted
  have actualMass := SourcePruningEnumerationRecursiveReservation.head_mass_le seed capturedMass inherited
    before scs receipt initialMass inheritedLength cacheBounds
  have mass : suspendedBound after.core ≤ massCeil seed capturedMass inherited := by
    simpa only [completed] using actualMass
  exact ⟨actualReceipt.completed, actualAdmitted.2.2.1,
    actualReceipt.bounded, actualReceipt.known, mass, reserved.2⟩

end MicroCFTA.SourcePruningEnumerationNativeHookResources
