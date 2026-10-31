import MicroCFTA.SourceCurrentAllocatedNativeStoredTerminal
import MicroCFTA.SourcePruningEnumerationChildAdmission

/-!
# Native structural certificates at every actual child return

The actual terminal partition derives its admission from the original bucket.
Empty and nonterminal branches retain the original caller.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredChildDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}

/-- Every actual child outcome retains native certificates under its current reservation. -/
theorem child_dispatch_native_stored
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
    (stored : Stored beforeCaller.checked.native) :
    Stored (SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming
      beforeCaller before memos.query).1.2.1.checked.native := by
  rw [SourcePruningEnumerationChildDispatch.erase checkEmpty r n p h k bucket incoming
    beforeCaller before memos.query]
  by_cases empty : incoming = .empty
  · simpa only [SourcePruningEnumerationChildDispatch.observe, ite_eq_left empty] using stored
  · cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil =>
        cases prepared : SourcePruningEnumerationShallowChild.prepareChild
            (EnumGuard := Constraint) bucket incoming <;>
          simpa only [SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty,
            partitioned, prepared] using stored
      | cons first rest =>
        have subsets := SourcePruningEnumerationChildCompletion.partition_subsets
          bucket first rest descendants partitioned
        have activeBounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter :=
          fun sc member => bounded sc (subsets.1 member)
        have activePending : InputsPending before.core (first :: rest) := by
          intro held fragment stored sc member
          exact pending held fragment stored sc (subsets.1 member)
        have reservation : Reserved bits seed ((first :: rest).length + 1) :=
          reserved.prefix (Nat.add_le_add_right
            (SourcePruningEnumerationChildCompletion.terminal_length_le
              bucket first rest descendants partitioned) 1)
        simpa only [SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty,
          partitioned] using
          SourceCurrentAllocatedNativeStoredTerminal.terminal_native_stored seed formulas solver inventory
            beforeCaller before.core checkEmpty r n p h first rest before.waiting incoming descendants
            roots memos initial safe paths counts activeBounded activePending realized available closed
            fits reservation known stored

end MicroCFTA.SourceCurrentAllocatedNativeStoredChildDispatch
