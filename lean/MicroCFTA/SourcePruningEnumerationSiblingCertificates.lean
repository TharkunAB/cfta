import MicroCFTA.SourcePruningEnumerationHeadOneResources
import MicroCFTA.SourcePruningEnumerationSiblingReservation

/-!
# Certificates at actual sibling endpoints

Each receipt keeps its own head endpoint and full memos. Each emitted
output keeps its own cache at the completed callback stage. A stopped
callback keeps its exact receipt, outputs, reason and optional endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeSiblingResources
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds)
open SourcePruningEnumerationRecursive (Output Failure OutputResources OutcomeResources)
open SourcePruningEnumerationSiblingReservation (stage stage_succ)
attribute [local irreducible] SourcePruningEnumerationRecursiveReservation.afterHook
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
local notation "afterHook" => SourcePruningEnumerationRecursiveReservation.afterHook
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Each processed receipt keeps its actual head endpoint and original cache bounds. -/
def ReceiptAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (before : Cached) (uv : Nat)
    (seed : Seed) (scs : List Suspended) (capturedMass inherited : Nat)
    (index : Nat) (receipt : Receipt width) : Prop :=
  Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
    HeadCacheBounds before scs (scalar (stage seed capturedMass inherited index).2)
      (guardWidth (stage seed capturedMass inherited index).1) receipt ∧
    ∃ (reached : Caller width) (saved : Queries) (next : Inventory) (final : Memos),
      advance receipt = some (reached, saved) ∧
      Post formulas solver next caller reached final ∧ final.query = saved ∧
      Fits (afterHead (stage seed capturedMass inherited index) inherited).2 reached.checked ∧
      Heap (fun guard => guard ∈ (afterHead (stage seed capturedMass inherited index) inherited).1)
        reached.checked.native.machine.heap

/-- Each output keeps its actual cache and the resources after its callback stage. -/
def OutputAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (seed : Seed) (capturedMass inherited index : Nat)
    (output : Output width Typing) : Prop :=
  OutputResources formulas solver caller (stage seed capturedMass inherited (index + 1)) output

/-- A stopped callback retains its own outputs inside the full ordered output prefix. -/
def StoppedAt
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
      ReceiptAt formulas solver caller before uv seed scs capturedMass inherited index receipt ∧
      OutcomeResources formulas solver caller (stage seed capturedMass inherited (index + 1))
        (.stopped hookOutputs reason endpoint)

variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {caller middle : Caller width} {before : Cached} {uv : Nat}
variable {seed : Seed} {capturedMass inherited index : Nat} {scs : List Suspended}
variable {middleInventory : Inventory} {middleMemos : Memos}

/-- A suffix receipt retains its head endpoint under the actual earlier native Post. -/
theorem ReceiptAt.prepend
    (post : Post formulas solver middleInventory caller middle middleMemos)
    {receipt : Receipt width}
    (certificate : ReceiptAt formulas solver middle before uv
      (afterHook seed capturedMass inherited) scs capturedMass inherited index receipt) :
    ReceiptAt formulas solver caller before uv seed scs capturedMass inherited (index + 1) receipt := by
  obtain ⟨admitted, pending, history, bounds, reached, saved, next, final,
    advanced, receiptPost, query, fits, known⟩ := certificate
  refine ⟨admitted, pending, history, ?_, reached, saved, next, final,
    advanced, post.trans receiptPost, query, ?_, ?_⟩
  · simpa only [stage_succ] using bounds
  · simpa only [stage_succ] using fits
  · simpa only [stage_succ] using known

/-- A suffix output retains its actual metadata, cache and full memos. -/
theorem OutputAt.prepend
    (post : Post formulas solver middleInventory caller middle middleMemos)
    {output : Output width Typing}
    (certificate : OutputAt formulas solver middle
      (afterHook seed capturedMass inherited) capturedMass inherited index output) :
    OutputAt formulas solver caller seed capturedMass inherited (index + 1) output := by
  unfold OutputAt at certificate ⊢
  simpa only [stage_succ] using certificate.post post

/-- A stopped suffix keeps its exact hook outputs and optional endpoint after prepending. -/
theorem StoppedAt.prepend
    (post : Post formulas solver middleInventory caller middle middleMemos)
    (headOutputs : List (Output width Typing))
    {outputs : List (Output width Typing)}
    {current : Stop (Failure width Typing) width}
    (certificate : StoppedAt formulas solver middle before uv
      (afterHook seed capturedMass inherited) scs capturedMass inherited index outputs current) :
    StoppedAt formulas solver caller before uv seed scs capturedMass inherited (index + 1)
      (headOutputs ++ outputs) current := by
  rcases certificate with unsupported |
    ⟨receipt, reason, endpoint, hookOutputs, prefixOutputs, same, ordered, receiptCertificate, resources⟩
  · exact .inl unsupported
  · refine .inr ⟨receipt, reason, endpoint, hookOutputs, headOutputs ++ prefixOutputs,
      same, ?_, receiptCertificate.prepend post, ?_⟩
    · simpa only [List.append_assoc] using congrArg (fun tail => headOutputs ++ tail) ordered
    · simpa only [stage_succ] using resources.post post

end MicroCFTA.SourcePruningEnumerationNativeSiblingResources
