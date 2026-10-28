import MicroCFTA.SourcePruningEnumerationFiniteSiblingCertificates
import MicroCFTA.SourcePruningEnumerationPreparedOutcomeResources
import MicroCFTA.SourcePruningEnumerationFiniteReservation

/-!
# Exact stopped callbacks for prepared finite siblings

Each receipt keeps its own head endpoint and full memos. Each emitted
output keeps its own cache at the completed finite callback stage. A stopped
callback keeps its exact receipt, outputs, reason and optional endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds)
open SourcePruningEnumerationRecursive (Output)
open SourcePruningEnumerationPreparedRecursive (Failure OutcomeResources)
open SourcePruningEnumerationNativeFiniteSiblingResources (ReceiptAt OutputAt)
open SourcePruningEnumerationFiniteReservation (stage stage_succ)
attribute [local irreducible] SourcePruningEnumerationFiniteReservation.step
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Stop" => SourcePruningEnumerationNativeContinuations.Stop
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "afterHook" => SourcePruningEnumerationFiniteReservation.step
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A stopped callback retains its own outputs inside the full ordered output prefix. -/
def StoppedAt (recursiveFuel : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (before : Cached) (uv : Nat)
    (seed : Seed) (scs : List Suspended) (capturedMass inherited index : Nat)
    (outputs : List (Output width Typing)) (current : Stop (Failure width Typing) width) : Prop :=
  current = .edge (some .unhandled) ∨
    ∃ (receipt : Receipt width) (reason : Failure width Typing)
      (endpoint : Option (Caller width × Queries))
      (hookOutputs prefixOutputs : List (Output width Typing)),
      current = .continuation receipt reason endpoint ∧ outputs = prefixOutputs ++ hookOutputs ∧
      ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited index receipt ∧
      OutcomeResources formulas solver caller (stage recursiveFuel seed capturedMass inherited (index + 1))
        (.stopped hookOutputs reason endpoint)

variable {recursiveFuel : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {caller middle : Caller width} {before : Cached} {uv : Nat}
variable {seed : Seed} {capturedMass inherited index : Nat} {scs : List Suspended}
variable {middleInventory : Inventory} {middleMemos : Memos}

/-- A stopped suffix keeps its exact hook outputs and optional endpoint after prepending. -/
theorem StoppedAt.prepend
    (post : Post formulas solver middleInventory caller middle middleMemos)
    (headOutputs : List (Output width Typing))
    {outputs : List (Output width Typing)}
    {current : Stop (Failure width Typing) width}
    (certificate : StoppedAt recursiveFuel formulas solver middle before uv
      (afterHook recursiveFuel seed capturedMass inherited) scs capturedMass inherited index outputs current) :
    StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited (index + 1)
      (headOutputs ++ outputs) current := by
  rcases certificate with unsupported |
    ⟨receipt, reason, endpoint, hookOutputs, prefixOutputs, same, ordered, receiptCertificate, resources⟩
  · exact .inl unsupported
  · refine .inr ⟨receipt, reason, endpoint, hookOutputs, headOutputs ++ prefixOutputs,
      same, ?_, receiptCertificate.prepend post, ?_⟩
    · simpa only [List.append_assoc] using congrArg (fun tail => headOutputs ++ tail) ordered
    · simpa only [stage_succ] using resources.post post

end MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources
