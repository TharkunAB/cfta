import MicroCFTA.SourceCurrentTerminalCapturedKnown
import MicroCFTA.SourceCurrentAllocatedNativeStoredChildDispatch
import MicroCFTA.SourceSizedPrefixOrdinaryIncomingInputs

/-! Original selected-parent facts retain the captured cache at the first actual child return. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentFirstChildCapturedKnown
open EnumerationState EnumerationCorrectness EnumerationCompleteness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
attribute [local instance] FormulaExecutable.formulaDecidableEq
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

private theorem terminal_length (scs : List Suspended) :
    (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1.length ≤ scs.length := by
  simpa only [List.partition_eq_filter_filter] using
    List.length_filter_le (fun sc : Suspended => EqualityTrie.isTerminal sc.trie) scs

private theorem terminal_subset (scs : List Suspended) (sc : Suspended)
    (member : sc ∈ (scs.partition (fun held => EqualityTrie.isTerminal held.trie)).1) : sc ∈ scs := by
  rw [List.partition_eq_filter_filter] at member
  exact (List.mem_filter.mp member).1

variable {bits : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- The literal child return retains its input cache and finite native storage on every outcome. -/
theorem child_captured (bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (checkEmpty : Bool) (r n p h k : Nat) (incoming : Node) (scs : List Suspended) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 caller.checked) (reserved : Reserved bits seed (scs.length + 1))
    (annotated : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (stored : Stored caller.checked.native) (known : KnownOrdinary bound caller.checked.native.machine.heap before) :
    let actual := SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs incoming caller before memos.query
    Stored actual.1.2.1.checked.native ∧ KnownOrdinary bound actual.1.2.1.checked.native.machine.heap before := by
  letI : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
  constructor
  · exact SourceCurrentAllocatedNativeStoredChildDispatch.child_dispatch_native_stored seed formulas solver inventory
      caller before checkEmpty r n p h k scs incoming roots memos initial safe paths counts realized bounded pending
      available closed fits reserved annotated stored
  · rw [SourcePruningEnumerationChildDispatch.erase]
    by_cases empty : incoming = .empty
    · simpa only [SourcePruningEnumerationChildDispatch.observe, ite_eq_left empty] using known
    · simp only [SourcePruningEnumerationChildDispatch.observe, ite_eq_right empty]
      cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
      | mk terminals descendants =>
          cases terminals with
          | nil =>
              cases actionEq : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming <;>
                simpa only [partitioned, actionEq] using known
          | cons first rest =>
              have subset : ∀ sc ∈ first :: rest, sc ∈ scs := by
                intro sc member
                apply terminal_subset scs sc
                simpa only [partitioned] using member
              have lengthBound : (first :: rest).length ≤ scs.length := by
                simpa only [partitioned] using terminal_length scs
              have terminalKnown := SourceCurrentTerminalCapturedKnown.terminal_captured bound seed formulas solver inventory
                caller before checkEmpty r n p h first rest incoming descendants roots memos initial safe paths counts
                (fun sc member => bounded sc (subset sc member))
                (fun held fragment recorded sc member => pending held fragment recorded sc (subset sc member))
                realized available closed fits (reserved.prefix (Nat.add_le_add_right lengthBound 1)) annotated stored known
              simpa only [partitioned] using terminalKnown

open scoped Classical in
/-- Original preparation facts certify the same captured prepared cache at the first child return. -/
theorem selected_first_child_captured (bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (parentSlot parentHandle : Nat) (scs : List Suspended) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (initial : Context formulas solver inventory caller memos)
    (known : KnownOrdinary bound caller.checked.native.machine.heap before)
    (parent : before.core.values[parentSlot]? = some (.unenumerated (some parentHandle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap parentHandle = some (.node entry edges depth free))
    (selected : edge ∈ InternedEdgeResidency.nodeEdges (.node entry edges depth free))
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked) (stored : Stored caller.checked.native)
    (annotated : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (reserved : Reserved bits seed
      (((SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).head?.getD (.empty, [])).2.length + 1)) :
    ∃ staged after, SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((edge.entry.key.symbol, staged, residual), after)] ∧
      ∀ incoming bucket rest, staged.map (fun input => (input.1, input.2.1)) = (incoming, bucket) :: rest →
        MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height (.node entry edges depth free) ∧
        ∀ checkEmpty r n p h k,
          let actual := SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming caller after memos.query
          Stored actual.1.2.1.checked.native ∧ KnownOrdinary bound actual.1.2.1.checked.native.machine.heap after := by
  letI : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
  obtain ⟨staged, after, prepared, inputs, safeAfter, pathsAfter, realizedAfter, countsAfter, _flagsAfter,
    knownAfter, inputFacts⟩ := SourceSizedPrefixOrdinaryIncomingInputs.complete bound caller.checked.native.machine.heap before
      known parentSlot parentHandle scs parent entry edges depth free decoded edge selected roots
      initial.ready.good.heap safe realized paths counts flags bounded pending allowed tries residual projected
  refine ⟨staged, after, prepared, ?_⟩
  intro incoming bucket rest head
  have originalHead := inputs.symm.trans head
  obtain ⟨available, closed, _ordinary, smaller, _height, allocated, pendingAfter⟩ :=
    inputFacts incoming bucket (by rw [head]; exact List.mem_cons_self)
  refine ⟨smaller, ?_⟩
  intro checkEmpty r n p h k
  apply child_captured bound seed formulas solver inventory caller after memos checkEmpty r n p h k incoming bucket roots
    initial safeAfter pathsAfter countsAfter allocated pendingAfter realizedAfter available closed fits
  · simpa only [originalHead, List.head?_cons, Option.getD_some] using reserved
  · exact annotated
  · exact stored
  · exact knownAfter

end MicroCFTA.SourceCurrentFirstChildCapturedKnown
