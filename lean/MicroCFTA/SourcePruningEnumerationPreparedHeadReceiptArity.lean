import MicroCFTA.SourcePruningEnumerationPreparedHeadAdmission
import MicroCFTA.SourcePruningEnumerationSelectedEdgeResourcesArity

/-!
# Forward arity through an actual prepared completed head

The prepared parent supplies its own availability and closedness.
The selected-edge resource producer retains the entire reached arity heap.
A common work bound identifies the caller of the actual captured completion.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq (Value Symbol Constraint)]

/-- An actual prepared head derives returned arity from the arity of its own input caller. -/
theorem CompletedHeadReceipt.arity_after
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
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata
      before checkEmpty uv handle scs parentEntry edges depth free edge bound fragment reached
      saved after returnedInventory returnedMemos)
    (heap : ArityHeap caller.checked.native.machine.heap) :
    ArityHeap reached.checked.native.machine.heap := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := receipt.admission.packet.valid
  obtain ⟨tries, residual, projected⟩ := receipt.projected
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    receipt.admission.ready.safe.1.values _ (List.mem_of_getElem? receipt.admission.stored)
  have pending := EnumerationReferences.pending_inputs before.core receipt.admission.packet.pending
    uv (some handle) scs receipt.admission.stored
  have reserved : Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, receipt.allowed,
      ↓reduceIte, projected] using receipt.admission.reserved
  obtain ⟨r, n, p, h, k, actualCaller, middle, actualSaved, _final, _next, _afterRoots, result,
    stable, _post, _query, _growth, _paths, _storage, _realized, _counts, _flags,
    _origin, _inputsPending, _protected, _pendingHistory, _incomingHistory, shape,
    _fits, _known, returnedArity⟩ :=
    SourcePruningEnumerationSelectedEdge.complete_with_fragments_resources_arity
      seed formulas solver inventory caller before checkEmpty parentEntry edges depth free edge scs roots memos
      receipt.admission.packet.context receipt.admission.parentAvailable receipt.admission.parentClosed
      receipt.admission.selected receipt.admission.packet.safe realized paths counts flags bounded pending
      receipt.allowed tries residual projected receipt.admission.bounded reserved receipt.admission.known heap
  let work := bound + (r + n + p + h + k)
  have rLe : r ≤ work := by dsimp [work]; omega
  have nLe : n ≤ work := by dsimp [work]; omega
  have pLe : p ≤ work := by dsimp [work]; omega
  have hLe : h ≤ work := by dsimp [work]; omega
  have kLe : k ≤ work := by dsimp [work]; omega
  have selectedAt : SourcePruningEnumerationSelectedEdge.run checkEmpty work work work work work
      scs edge caller before memos.query = result := by
    simpa only [Nat.add_sub_of_le rLe, Nat.add_sub_of_le nLe, Nat.add_sub_of_le kLe] using
      stable (work - r) (work - n) work work (work - k) pLe hLe
  have capturedAt : SourcePruningEnumerationCapturedEdge.run checkEmpty work work work work work
      uv scs edge caller before memos.query = some (.complete fragment reached saved after) :=
    receipt.running (r + n + p + h + k)
  rw [SourcePruningEnumerationCapturedEdge.run, selectedAt] at capturedAt
  rcases shape with ⟨produced, completed, _safe, _bounded, _pending, _separate⟩ |
    ⟨_fragments, _outer, _waiting, stopped⟩
  · rw [completed] at capturedAt
    obtain ⟨finished, _finalized, fields⟩ := Option.map_eq_some_iff.mp capturedAt
    have callerSame : actualCaller = reached :=
      (SourcePruningEnumerationSelectedEdge.Result.complete.inj fields).2.1
    simpa only [callerSame] using returnedArity
  · rw [stopped] at capturedAt
    cases capturedAt

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
