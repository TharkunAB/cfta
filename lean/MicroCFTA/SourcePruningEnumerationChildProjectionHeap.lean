import MicroCFTA.SourcePruningEnumerationChildObservedResources
import MicroCFTA.SourcePruningEnumerationTerminalProjectionHeap

/-!
# Projection heaps at actual child returns

Empty and shallow branches retain the original native caller.
The terminal branch uses its actual fold and incoming query endpoint.
Cache erasure retains that caller even when the cache candidate is absent.
-/
namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))
variable {bits : Nat}

/-- Actual outer child successes retain the original resource pair and their reached projection heap. -/
theorem observed_resources_projection_heap
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h k : Nat) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (bucket.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap beforeCaller.checked.native.machine.heap)
    {result : Option TerminalRaw} {afterCaller : Caller (bits + 2)} {savedQueries : Queries}
    {outer : EnumerationState.State Symbol Constraint} {moved : EnumerationWaitingIndex.Waiting}
    {cache : Option Cached}
    (observed : run checkEmpty r n p h k bucket incoming beforeCaller before memos.query =
      ((.ok result, afterCaller, savedQueries, outer, moved), cache)) :
    Fits (advance seed (bucket.length + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1)
        afterCaller.checked.native.machine.heap ∧
      ProjectionHeap afterCaller.checked.native.machine.heap := by
  have resources := observed_resources seed formulas solver inventory beforeCaller before
    checkEmpty r n p h k bucket incoming roots memos initial safe paths counts realized bounded pending
    available closed fits reserved known observed
  refine ⟨resources.1, resources.2, ?_⟩
  clear resources
  have original : observe checkEmpty r n p h bucket incoming beforeCaller before.core
      before.waiting memos.query = (.ok result, afterCaller, savedQueries, outer, moved) := by
    rw [← erase checkEmpty r n p h k bucket incoming beforeCaller before memos.query]
    exact congrArg Prod.fst observed
  have unchanged : ProjectionHeap beforeCaller.checked.native.machine.heap := originalProjection
  by_cases empty : incoming = .empty
  · simp only [observe, ite_eq_left empty] at original
    have callerSame := congrArg (fun output => output.2.1) original
    dsimp only at callerSame
    rw [← callerSame]
    exact unchanged
  · cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        cases prepared : SourcePruningEnumerationShallowChild.prepareChild
            (EnumGuard := Constraint) bucket incoming <;>
          simp only [observe, ite_eq_right empty, partitioned, prepared] at original
        all_goals
          have callerSame := congrArg (fun output => output.2.1) original
          dsimp only at callerSame
          rw [← callerSame]
          exact unchanged
      | cons first rest =>
        have subsets := SourcePruningEnumerationChildCompletion.partition_subsets
          bucket first rest descendants partitioned
        have activeBounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter :=
          fun sc member => bounded sc (subsets.1 member)
        have activePending : InputsPending before.core (first :: rest) := by
          intro held fragment stored sc member
          exact pending held fragment stored sc (subsets.1 member)
        have lengthBound := SourcePruningEnumerationChildCompletion.terminal_length_le
          bucket first rest descendants partitioned
        have reservation : Reserved bits seed ((first :: rest).length + 1) :=
          reserved.prefix (by omega)
        have actualTerminal : SourcePruningEnumerationTerminal.run checkEmpty r n p h first rest
            before.waiting beforeCaller before.core incoming descendants memos.query =
            (.ok result, afterCaller, savedQueries, outer, moved) := by
          simpa only [observe, ite_eq_right empty, partitioned] using original
        exact (SourcePruningEnumerationTerminal.observed_resources_projection_heap seed formulas solver inventory
          beforeCaller before.core checkEmpty r n p h first rest before.waiting incoming descendants roots memos
          initial safe paths counts activeBounded activePending realized available closed fits reservation known
          originalProjection actualTerminal).2.2

end MicroCFTA.SourcePruningEnumerationChildDispatch
