import MicroCFTA.SourcePruningEnumerationPreparedHeadAdmission
import MicroCFTA.SourcePruningEnumerationCapturedPreparedProjectionHeap

/-!
# Projection at the actual prepared completed-head caller

The prepared parent supplies its own availability and closure.
The original stored handle remains separate from that parent.
The literal completed execution identifies the reached native heap.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]

/-- An actual prepared head retains projection from its original input caller. -/
theorem CompletedHeadReceipt.projection_heap
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller reached : Caller (bits + 2)} {memos returnedMemos : Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before after : Cached}
    {checkEmpty : Bool} {uv handle : Nat} {scs : List Suspended}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {edges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {saved : SourceEndpointMemo.Memos}
    {returnedInventory : Inventory}
    (head : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata
      before checkEmpty uv handle scs parentEntry edges depth free edge bound fragment reached
      saved after returnedInventory returnedMemos)
    (originalProjection : ProjectionHeap caller.checked.native.machine.heap) :
    ProjectionHeap reached.checked.native.machine.heap := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := head.admission.packet.valid
  obtain ⟨tries, residual, projected⟩ := head.projected
  have pending := EnumerationReferences.pending_inputs before.core head.admission.packet.pending
    uv (some handle) scs head.admission.stored
  have actualReserved : Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, head.allowed,
      ↓reduceIte, projected] using head.admission.reserved
  have current := SourcePruningEnumerationCapturedEdge.run_prepared_projection_heap seed formulas solver inventory
    caller before checkEmpty uv handle scs parentEntry edges depth free edge roots memos
    head.admission.packet.context head.admission.ready head.admission.stored
    head.admission.parentAvailable head.admission.parentClosed realized head.admission.selected paths counts flags
    pending head.allowed tries residual projected head.admission.bounded actualReserved head.admission.known
    originalProjection bound bound bound bound bound
  have actual := head.running 0
  simp only [Nat.add_zero] at actual
  simpa only [actual] using current

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
