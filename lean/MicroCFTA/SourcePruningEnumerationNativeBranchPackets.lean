import MicroCFTA.SourcePruningEnumerationNativeBranchResources
import MicroCFTA.SourcePruningEnumerationRecursivePacket

/-!
# Recursive packets at each completed alternative

Each completed receipt retains its own cache, caller and full memo state.
The original captured cache remains valid at that same native endpoint.
The resource forecast follows that receipt's exact processed prefix.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationNativeBranches (advance)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original packets derive both recursive cache views at each actual completed receipt. -/
theorem complete_with_packets_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (cost scs before.core.counter selectedEdges))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (processed : List (Receipt (bits + 2))) (afterCaller : Caller (bits + 2)) (saved : Queries)
      (final : Memos) (next : Inventory) (result : Result (bits + 2)),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationNativeBranches.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧
      (∀ receipt ∈ processed, Admitted uv receipt) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        ∀ receipt ∈ processed, Pending receipt) ∧
      (∀ receipt ∈ processed,
        ∃ (reached : Caller (bits + 2)) (savedQueries : Queries) (receiptInventory : Inventory) (receiptMemos : Memos),
          advance receipt = some (reached, savedQueries) ∧
          Post formulas solver receiptInventory caller reached receiptMemos ∧ receiptMemos.query = savedQueries) ∧
      (∀ receipt ∈ processed, FragmentHistory before.core receipt) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) ∧
      Fits (reservationAdvance seed (cost scs before.core.counter selectedEdges)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter selectedEdges)).1)
        afterCaller.checked.native.machine.heap ∧
      (∀ (index : Nat) (receipt : Receipt (bits + 2)), processed[index]? = some receipt →
        ∃ (reached : Caller (bits + 2)) (savedQueries : Queries),
          advance receipt = some (reached, savedQueries) ∧
          Fits (reservationAdvance seed (cost scs before.core.counter (selectedEdges.take (index + 1)))).2
            reached.checked ∧
          Heap (fun guard => guard ∈
            (reservationAdvance seed (cost scs before.core.counter (selectedEdges.take (index + 1)))).1)
            reached.checked.native.machine.heap) ∧
      (∀ (metadata : Metadata Typing)
          (_packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before),
        EnumerationReferences.IncomingAvoid uv before.core →
        ∀ (index : Nat) (fragment : Fragment) (receiptCaller : Caller (bits + 2))
          (receiptQueries : Queries) (receiptCache : Cached),
          processed[index]? = some (.complete fragment receiptCaller receiptQueries receiptCache) →
          ∃ (receiptInventory : Inventory) (receiptMemos : Memos),
            Post formulas solver receiptInventory caller receiptCaller receiptMemos ∧
            receiptMemos.query = receiptQueries ∧
            SourcePruningEnumerationRecursive.Packet formulas solver receiptInventory
              receiptCaller receiptMemos metadata receiptCache ∧
            SourcePruningEnumerationRecursive.Packet formulas solver receiptInventory
              receiptCaller receiptMemos metadata before ∧
            Fits (SourcePruningEnumerationIncomingReservation.advance seed
              (cost scs before.core.counter (selectedEdges.take (index + 1)))).2 receiptCaller.checked ∧
            Heap (fun guard => guard ∈ (SourcePruningEnumerationIncomingReservation.advance seed
              (cost scs before.core.counter (selectedEdges.take (index + 1)))).1)
              receiptCaller.checked.native.machine.heap) := by
  obtain ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    running, post, querySame, admitted, pendingHistory, posts, fragmentHistory, shape, supported,
    returnedFits, returnedKnown, indexedResources⟩ :=
    complete_with_history_resources seed formulas solver inventory caller before checkEmpty uv handle scs
      parentEntry storedEdges selectedEdges depth free roots memos initial ready stored decoded realized selected
      paths counts flags pending fits reserved known
  refine ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    running, post, querySame, admitted, pendingHistory, posts, fragmentHistory, shape, supported,
    returnedFits, returnedKnown, indexedResources, ?_⟩
  intro metadata packet incoming index fragment receiptCaller receiptQueries receiptCache found
  have member : (.complete fragment receiptCaller receiptQueries receiptCache : Receipt (bits + 2)) ∈ processed :=
    List.mem_of_getElem? found
  obtain ⟨reached, actualQueries, receiptInventory, receiptMemos, postAdvance, receiptPost, receiptQuery⟩ :=
    posts _ member
  have postEndpoint : (receiptCaller, receiptQueries) = (reached, actualQueries) :=
    Option.some.inj postAdvance
  obtain ⟨postCaller, postQueries⟩ := Prod.mk.inj postEndpoint
  rw [← postCaller] at receiptPost
  rw [← postQueries] at receiptQuery
  obtain ⟨resourceCaller, _resourceQueries, resourceAdvance, receiptFits, receiptKnown⟩ :=
    indexedResources index _ found
  have resourceEndpoint : receiptCaller = resourceCaller :=
    (Prod.mk.inj (Option.some.inj resourceAdvance)).1
  rw [← resourceEndpoint] at receiptFits receiptKnown
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  have ownPacket : SourcePruningEnumerationRecursive.Packet formulas solver receiptInventory
      receiptCaller receiptMemos metadata receiptCache :=
    SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment receiptCache level frontier
      receiptPost.context (by simpa only [receiptQuery] using admitted _ member)
      (by simpa only [receiptQuery] using fragmentHistory _ member)
      (pendingHistory packet.pending incoming _ member) ordered packet.bounded
  exact ⟨receiptInventory, receiptMemos, receiptPost, receiptQuery, ownPacket,
    SourcePruningEnumerationRecursive.captured_post packet receiptPost, receiptFits, receiptKnown⟩

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
