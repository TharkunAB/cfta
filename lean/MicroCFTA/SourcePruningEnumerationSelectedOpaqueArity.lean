import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationChildObservedArity

/-!
# Arity at an actual prepared opaque completion

The actual child observation supplies its reached native caller.
The captured-target finalizer retains that caller.
The original stored handle is separate from the prepared input value.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original local resources retain native arity at the same actual completed opaque endpoint. -/
theorem complete_heap (seed : Seed)
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller reached : Caller (bits + 2)} {memos : Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before after : Cached}
    {checkEmpty : Bool} {r n p h k target originalHandle : Nat} {scs : List Suspended}
    {value : Node} {fragment : Fragment} {saved : Queries}
    (packet : Packet formulas solver inventory caller memos metadata before)
    (stored : before.core.values[target]? = some (.unenumerated (some originalHandle) scs))
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (bounded : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (scs.length + 1))
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      caller.checked.native.machine.heap)
    (arity : ArityHeap caller.checked.native.machine.heap)
    (completed : run checkEmpty r n p h k target scs value caller before memos.query =
      some (.complete fragment reached saved after)) : ArityHeap reached.checked.native.machine.heap := by
  obtain ⟨roots, paths, _storage, realized, counts, _flags⟩ := packet.valid
  have bucketBound : ∀ sc ∈ scs, sc.var < before.core.counter :=
    packet.safe.1.values _ (List.mem_of_getElem? stored)
  have pendingInputs := EnumerationReferences.pending_inputs before.core packet.pending
    target (some originalHandle) scs stored
  have finalize (produced : Fragment) (returned outer : Core)
      (childCaller : Caller (bits + 2)) (childQueries : Queries)
      (waiting : EnumerationWaitingIndex.Waiting) (middle : Cached)
      (childRun : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs value caller before memos.query =
        ((.ok (some [.ok (produced, returned)]), childCaller, childQueries, outer, waiting), some middle))
      (observed : (SourcePruningEnumerationFinalize.run childCaller.checked.native.machine.heap k target produced middle).map
        (fun finished => SourcePruningEnumerationSelectedEdge.Result.complete produced childCaller childQueries finished) =
          some (.complete fragment reached saved after)) : ArityHeap reached.checked.native.machine.heap := by
    have childHeap := SourcePruningEnumerationChildDispatch.observed_heap seed formulas solver inventory
      caller before checkEmpty r n p h k scs value roots memos packet.context packet.safe paths counts
      realized bucketBound pendingInputs available closed bounded reserved known arity childRun
    obtain ⟨finished, _finishing, fields⟩ := Option.map_eq_some_iff.mp observed
    have callerSame : childCaller = reached :=
      (SourcePruningEnumerationSelectedEdge.Result.complete.inj fields).2.1
    rw [← callerSame]
    exact childHeap
  cases value with
  | empty =>
    simp only [run, ↓reduceIte, Option.some.injEq, reduceCtorEq] at completed
  | reference | mu | union =>
    simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at completed
    split at completed
    next produced returned childCaller childQueries outer waiting middle childRun =>
      exact finalize produced returned outer childCaller childQueries waiting middle childRun completed
    next => cases completed
  | node entry edges depth free =>
    cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
    | true =>
      simp only [run, reduceCtorEq, terminal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at completed
      split at completed
      next produced returned childCaller childQueries outer waiting middle childRun =>
        exact finalize produced returned outer childCaller childQueries waiting middle childRun completed
      next => cases completed
    | false =>
      rw [ordinary_deferred checkEmpty r n p h k target scs entry edges depth free
        caller before memos.query terminal] at completed
      cases completed

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
