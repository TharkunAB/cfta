import MicroCFTA.SourcePruningEnumerationNativeBranchResources
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationRecursive

/-!
# Certificates for actual hook-aware alternatives

Each processed receipt and emitted output keeps its own native endpoint.
A stopped callback keeps its current receipt outside the processed prefix.
The original ordered edge prefix bounds each reached native heap.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory cost)
open SourcePruningEnumerationRecursive (Packet Output Failure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A processed receipt retains its own full Post and original edge-prefix resources. -/
def ReceiptAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (before : Cached) (uv : Nat) (seed : Seed) (scs : List Suspended)
    (edges : List (EdgeValue Symbol Constraint)) (index : Nat) (receipt : Receipt width) : Prop :=
  Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
  ∃ (reached : Caller width) (saved : SourceEndpointMemo.Memos) (next : Inventory) (final : Memos),
    advance receipt = some (reached, saved) ∧ Post formulas solver next caller reached final ∧
    final.query = saved ∧
    Fits (reservationAdvance seed (cost scs before.core.counter (edges.take (index + 1)))).2 reached.checked ∧
    Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter (edges.take (index + 1)))).1)
      reached.checked.native.machine.heap

/-- An emitted output retains its actual metadata packet and native edge-prefix resources. -/
def OutputAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (before : Cached) (seed : Seed) (scs : List Suspended)
    (edges : List (EdgeValue Symbol Constraint)) (index : Nat) (output : Output width Typing) : Prop :=
  ∃ (next : Inventory) (final : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing),
    Post formulas solver next caller output.caller final ∧ final.query = output.queries ∧
    Packet formulas solver next output.caller final metadata output.cache ∧
    (output.metadata = none ∨ output.metadata = some metadata) ∧
    Fits (reservationAdvance seed (cost scs before.core.counter (edges.take (index + 1)))).2 output.caller.checked ∧
    Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter (edges.take (index + 1)))).1)
      output.caller.checked.native.machine.heap

/-- Unsupported edges and exhausted hooks retain different exact stopping observations. -/
def StoppedAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (before : Cached) (uv : Nat) (seed : Seed) (scs : List Suspended)
    (edges : List (EdgeValue Symbol Constraint)) (index : Nat)
    (reached : Caller width) (next : Inventory) (final : Memos)
    (current : SourcePruningEnumerationNativeContinuations.Stop (Failure width Typing) width) : Prop :=
  current = .edge (some .unhandled) ∨
  ∃ (fragment : Fragments.Fragment Symbol) (receiptCache : Cached) (selected : Nat)
    (updated : SourcePruningRecordTypes.Metadata Typing) (callbackCache : Cached),
    current = .continuation (.complete fragment reached final.query receiptCache)
      (.exhausted selected updated callbackCache) (some (reached, final.query)) ∧
    ReceiptAt formulas solver caller before uv seed scs edges index
      (.complete fragment reached final.query receiptCache) ∧
    Packet formulas solver next reached final updated callbackCache

variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {caller middle : Caller width} {before : Cached} {uv : Nat} {seed : Seed} {scs : List Suspended}
variable {edge : EdgeValue Symbol Constraint} {rest : List (EdgeValue Symbol Constraint)} {index : Nat}
variable {middleInventory : Inventory} {middleMemos : Memos}

/-- A suffix receipt retains its own endpoint under the original caller and edge prefix. -/
theorem ReceiptAt.prepend (post : Post formulas solver middleInventory caller middle middleMemos)
    {receipt : Receipt width}
    (certificate : ReceiptAt formulas solver middle before uv
      (reservationAdvance seed (SourcePruningEnumerationNativeBranchCompletion.edgeCost scs before.core.counter edge))
      scs rest index receipt) :
    ReceiptAt formulas solver caller before uv seed scs (edge :: rest) (index + 1) receipt := by
  obtain ⟨admitted, pending, history, reached, saved, next, final, advanced, receiptPost, query, fits, known⟩ := certificate
  refine ⟨admitted, pending, history, reached, saved, next, final, advanced, post.trans receiptPost, query, ?_, ?_⟩
  · simpa only [List.take_succ_cons, cost, SourcePruningEnumerationIncomingReservation.advance_add] using fits
  · simpa only [List.take_succ_cons, cost, SourcePruningEnumerationIncomingReservation.advance_add] using known

/-- A suffix output keeps its callback cache and full memos at its own original prefix. -/
theorem OutputAt.prepend (post : Post formulas solver middleInventory caller middle middleMemos)
    {output : Output width Typing}
    (certificate : OutputAt formulas solver middle before
      (reservationAdvance seed (SourcePruningEnumerationNativeBranchCompletion.edgeCost scs before.core.counter edge))
      scs rest index output) :
    OutputAt formulas solver caller before seed scs (edge :: rest) (index + 1) output := by
  obtain ⟨next, final, metadata, outputPost, query, packet, shape, fits, known⟩ := certificate
  refine ⟨next, final, metadata, post.trans outputPost, query, packet, shape, ?_, ?_⟩
  · simpa only [List.take_succ_cons, cost, SourcePruningEnumerationIncomingReservation.advance_add] using fits
  · simpa only [List.take_succ_cons, cost, SourcePruningEnumerationIncomingReservation.advance_add] using known

/-- An exhausted suffix keeps the current unprocessed receipt and exact native endpoint. -/
theorem StoppedAt.prepend (post : Post formulas solver middleInventory caller middle middleMemos)
    {reached : Caller width} {next : Inventory} {final : Memos}
    {current : SourcePruningEnumerationNativeContinuations.Stop (Failure width Typing) width}
    (certificate : StoppedAt formulas solver middle before uv
      (reservationAdvance seed (SourcePruningEnumerationNativeBranchCompletion.edgeCost scs before.core.counter edge))
      scs rest index reached next final current) :
    StoppedAt formulas solver caller before uv seed scs (edge :: rest) (index + 1) reached next final current := by
  rcases certificate with stopped | ⟨fragment, receiptCache, selected, updated, callbackCache, same, receipt, packet⟩
  · exact .inl stopped
  · exact .inr ⟨fragment, receiptCache, selected, updated, callbackCache, same, receipt.prepend post, packet⟩

end MicroCFTA.SourcePruningEnumerationNativeHookResources
