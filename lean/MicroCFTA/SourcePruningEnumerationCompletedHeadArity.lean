import MicroCFTA.SourcePruningEnumerationHeadAdmission
import MicroCFTA.SourcePruningEnumerationNativeHeadResourcesArity

/-!
# Arity at the same stable completed-head endpoint

The receipt supplies its original current input and resource reservation.
A common bound aligns its stable run with the new arity producer.
The proof does not compare the current work fuel with a new completion bound.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]

/-- The original current head heap derives arity at the receipt's same reached caller. -/
theorem CompletedHeadReceipt.returned_heap
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragment} {reached : Caller (bits + 2)} {saved : Queries} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos)
    (initialArity : ArityHeap caller.checked.native.machine.heap) :
    ArityHeap reached.checked.native.machine.heap := by
  obtain ⟨handle, parentEntry, edges, depth, free, stored, decoded, selected⟩ := receipt.admission.source
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := receipt.admission.packet.valid
  have pending := EnumerationReferences.pending_inputs before.core receipt.admission.packet.pending
    uv (some handle) scs stored
  obtain ⟨r, n, p, h, k, actual, actualCaller, actualQueries, _actualMemos, _actualInventory,
    running, _post, _queries, _admitted, _pending, _history, shape, _fits, _known, returnedArity⟩ :=
    SourcePruningEnumerationNativeBranchCompletion.head_complete_resources_arity seed formulas solver inventory
      caller before checkEmpty uv handle scs parentEntry edges depth free edge roots memos
      receipt.admission.packet.context receipt.admission.ready stored decoded realized selected paths counts flags
      pending receipt.admission.bounded receipt.admission.reserved receipt.admission.known initialArity
  let common := bound + r + n + p + h + k
  have boundLe : bound ≤ common := by dsimp [common]; omega
  have rLe : r ≤ common := by dsimp [common]; omega
  have nLe : n ≤ common := by dsimp [common]; omega
  have pLe : p ≤ common := by dsimp [common]; omega
  have hLe : h ≤ common := by dsimp [common]; omega
  have kLe : k ≤ common := by dsimp [common]; omega
  have produced := running (common - r) (common - n) common common (common - k) pLe hLe
  rw [Nat.add_sub_of_le rLe, Nat.add_sub_of_le nLe, Nat.add_sub_of_le kLe] at produced
  have original := receipt.running (common - bound)
  rw [Nat.add_sub_of_le boundLe] at original
  have same : actual = .complete fragment reached saved after :=
    Option.some.inj (produced.symm.trans original)
  rcases shape with advanced | unhandled
  · rw [same] at advanced
    change some (reached, saved) = some (actualCaller, actualQueries) at advanced
    have callerSame := (Prod.mk.inj (Option.some.inj advanced)).1
    rw [callerSame]
    exact returnedArity
  · rw [same] at unhandled
    cases unhandled.1

end MicroCFTA.SourcePruningEnumerationNativeHookResources
