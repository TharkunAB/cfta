import MicroCFTA.SourcePruningEnumerationHeadAdmission
import MicroCFTA.SourcePruningEnumerationCapturedEdgeProjectionHeap

/-!
# Projection at the actual completed-head caller

The head receipt supplies its original packet and selected edge reservation.
Its literal completed execution identifies the same reached native caller.
The only heap premise applies to the original caller.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]

/-- The original caller projection reaches the same actual completed head endpoint. -/
theorem CompletedHeadReceipt.projection_heap
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragment} {reached : Caller (bits + 2)} {saved : Queries} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (head : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos)
    (originalProjection : ProjectionHeap caller.checked.native.machine.heap) :
    ProjectionHeap reached.checked.native.machine.heap := by
  obtain ⟨handle, parentEntry, edges, depth, free, stored, decoded, selected⟩ := head.admission.source
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := head.admission.packet.valid
  obtain ⟨tries, residual, projected⟩ := head.projected
  have pending := EnumerationReferences.pending_inputs before.core head.admission.packet.pending
    uv (some handle) scs stored
  have actualReserved : Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, head.allowed,
      ↓reduceIte, projected] using head.admission.reserved
  have current := SourcePruningEnumerationCapturedEdge.run_projection_heap seed formulas solver inventory
    caller before checkEmpty uv handle scs parentEntry edges depth free edge roots memos
    head.admission.packet.context head.admission.ready stored decoded realized selected paths counts flags
    pending head.allowed tries residual projected head.admission.bounded actualReserved head.admission.known
    originalProjection bound bound bound bound bound
  have actual := head.running 0
  simp only [Nat.add_zero] at actual
  simpa only [actual] using current

end MicroCFTA.SourcePruningEnumerationNativeHookResources
