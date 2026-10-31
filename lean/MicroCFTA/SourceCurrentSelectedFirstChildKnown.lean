import MicroCFTA.SourceSizedPrefixOrdinaryIncomingInputs
import MicroCFTA.SourceSizedPrefixOrdinaryChildCreation
import MicroCFTA.SourceCurrentAllocatedNativeTerminalKnown

/-! The selected parent's cache certifies the first literal child call.
This result does not choose a sufficient recursive depth. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentSelectedFirstChildKnown
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompleteness EnumerationDependencies InternedConstructorTemplates InternedProbeProvenance
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
local notation "Core" => EnumerationState.State Symbol Constraint
variable {bits : Nat}

private def ResultKnown (bound : Nat) (before : Cached)
    (actual : SourcePruningEnumerationChildDispatch.Observation (bits + 2) × Option Cached) : Prop :=
  (match actual.1.1 with
    | .ok (some rows) => ∀ fragment returned, Except.ok (fragment, returned) ∈ rows →
        KnownOrdinary bound actual.1.2.1.checked.native.machine.heap {before with core := returned}
    | _ => True) ∧
  (match actual.2 with
    | some after => KnownOrdinary bound actual.1.2.1.checked.native.machine.heap after
    | none => True)

private theorem partition_length (scs : List Suspended) :
    (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1.length ≤ scs.length := by
  simpa only [List.partition_eq_filter_filter] using
    List.length_filter_le (fun sc : Suspended => EqualityTrie.isTerminal sc.trie) scs

private theorem partition_subset (scs : List Suspended) :
    ∀ sc ∈ (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1, sc ∈ scs := by
  intro sc member
  rw [List.partition_eq_filter_filter] at member
  exact (List.mem_filter.mp member).1

variable [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem child_known (bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (checkEmpty : Bool) (r n p h k : Nat) (incoming : Node) (scs : List Suspended) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (ordinary : SourceCurrentAllocatedFiniteOrdinaryDomain.Node incoming)
    (height : MergedOrdinaryHeight.height incoming ≤ bound)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (fits : Fits seed.2 caller.checked) (reserved : Reserved bits seed (scs.length + 1))
    (annotated : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (stored : Stored caller.checked.native)
    (known : KnownOrdinary bound caller.checked.native.machine.heap before) :
    ResultKnown bound before
      (SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs incoming caller before memos.query) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Node) (fun a b => Classical.propDecidable (a = b))
  letI : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
  cases incoming with
  | empty => simpa [ResultKnown, SourcePruningEnumerationChildDispatch.run] using known
  | reference name => cases ordinary
  | union entry members depth free => cases ordinary
  | mu entry body depth ordinaryValue => cases ordinary
  | node entry edges depth free =>
    have nonempty : Value.node entry edges depth free ≠ .empty := by simp
    cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk terminals descendants => cases terminals with
      | cons first rest =>
        have lengthBound : (first :: rest).length ≤ scs.length := by
          simpa only [partitioned] using partition_length scs
        have subset : ∀ sc ∈ first :: rest, sc ∈ scs := by
          simpa only [partitioned] using partition_subset scs
        have resource := reserved.prefix (Nat.add_le_add_right lengthBound 1)
        have produced := SourceCurrentAllocatedNativeTerminalKnown.run_known bits bound seed formulas solver inventory
            caller before checkEmpty r n p h k first rest (.node entry edges depth free) descendants roots memos
            initial safe paths counts (fun sc member => bounded sc (subset sc member))
            (fun held fragment recorded sc member => pending held fragment recorded sc (subset sc member))
            realized available closed ordinary height fits resource annotated stored known
        simp only [ResultKnown, SourcePruningEnumerationChildDispatch.run, nonempty, ↓reduceIte, partitioned]
        constructor
        · cases observed : (SourcePruningEnumerationCachedTerminalAdapter.run checkEmpty r n p h k
              first rest caller before (.node entry edges depth free) descendants memos.query).1.1 with
          | error fault => trivial
          | ok possible => cases possible with
            | none => trivial
            | some results => simpa only [observed] using produced.1
        · cases observed : (SourcePruningEnumerationCachedTerminalAdapter.run checkEmpty r n p h k
              first rest caller before (.node entry edges depth free) descendants memos.query).2 with
          | none => trivial
          | some returned => simpa only [observed] using produced.2
      | nil =>
        by_cases nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
        · obtain ⟨handle, after, fuel, encoded, decoded, prepares, slot, grows, afterKnown⟩ :=
            SourceSizedPrefixOrdinaryChildCreation.prepareOrdinary_known bound caller.checked.native.machine.heap before
              entry edges depth free scs roots initial.ready.good.heap.semantic.1.normal.facts.coherent
              available closed safe.1 realized paths counts flags bounded nonterminal known ordinary height
          have cached : SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap
              fuel scs (.node entry edges depth free) before = some [(.hole before.core.counter, after)] := by
            simp only [SourcePruningEnumerationCachedPrepare.prepareChild]
            rw [show fuel = fuel + 0 by omega, prepares 0]
            rfl
          have raw := SourcePruningEnumerationCachedPrepare.erase_some caller.checked.native.machine.heap
            fuel scs (.node entry edges depth free) before _ cached
          simp only [List.map_cons, List.map_nil] at raw
          cases actionEq : (SourcePruningEnumerationShallowChild.prepareChild scs (.node entry edges depth free) :
              Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) with
          | none =>
            rw [actionEq] at raw
            contradiction
          | some action =>
            have actualRaw : ExceptT.run (action before.core) =
                [.ok (.hole before.core.counter, after.core)] := by
              simpa only [actionEq, Option.map_some, Option.some.injEq] using raw
            simp only [ResultKnown, SourcePruningEnumerationChildDispatch.run, nonempty, ↓reduceIte,
              partitioned, SourcePruningEnumerationChildDispatch.observe, actionEq]
            constructor
            · simp only [actualRaw]
              intro fragment returned member
              have same : returned = after.core :=
                congrArg Prod.snd (Except.ok.inj (List.mem_singleton.mp member))
              subst returned
              simpa only [KnownOrdinary] using afterKnown
            · cases actualEq : SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap
                k scs (.node entry edges depth free) before with
              | none => trivial
              | some actualRows => cases actualRows with
                | nil => exact known
                | cons first tail => cases tail with
                  | cons second rest => trivial
                  | nil =>
                    rcases first with ⟨fragment, returned⟩
                    have erased := SourcePruningEnumerationCachedPrepare.erase_some caller.checked.native.machine.heap
                      k scs (.node entry edges depth free) before _ actualEq
                    have same := raw.symm.trans erased
                    simp only [List.map_cons, List.map_nil, Option.some.injEq, List.cons.injEq,
                      Except.ok.injEq, Prod.mk.injEq, and_true] at same
                    simpa only [KnownOrdinary, same.2] using afterKnown
        · have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
            cases actual : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;> simp_all
          simp only [ResultKnown, SourcePruningEnumerationChildDispatch.run, nonempty, ↓reduceIte, partitioned,
            SourcePruningEnumerationChildDispatch.observe, SourcePruningEnumerationShallowChild.prepareChild,
            SourcePruningEnumerationCachedPrepare.prepareChild, SourcePruningEnumerationCachedChild.prepareOrdinary, terminal]; trivial

/-- Original selected-parent facts certify the first literal staged child and its actual returned core. -/
theorem selected_first_child (bound : Nat) (seed : Seed)
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
        ∀ checkEmpty r n p h k, ResultKnown bound after
          (SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming caller after memos.query) := by
  obtain ⟨staged, after, prepared, inputs, safeAfter, pathsAfter, realizedAfter, countsAfter, flagsAfter,
    knownAfter, inputFacts⟩ := SourceSizedPrefixOrdinaryIncomingInputs.complete bound caller.checked.native.machine.heap before
      known parentSlot parentHandle scs parent entry edges depth free decoded edge selected roots
      initial.ready.good.heap safe realized paths counts flags bounded pending allowed tries residual projected
  refine ⟨staged, after, prepared, ?_⟩
  intro incoming bucket rest head
  have originalHead := inputs.symm.trans head
  obtain ⟨available, closed, ordinary, smaller, height, allocated, pendingAfter⟩ :=
    inputFacts incoming bucket (by rw [head]; exact List.mem_cons_self)
  refine ⟨smaller, ?_⟩
  intro checkEmpty r n p h k
  apply child_known bound seed formulas solver inventory caller after memos checkEmpty r n p h k incoming bucket roots
    initial safeAfter pathsAfter countsAfter flagsAfter realizedAfter available closed ordinary height allocated pendingAfter fits
  · simpa only [originalHead, List.head?_cons, Option.getD_some] using reserved
  · exact annotated
  · exact stored
  · exact knownAfter

end MicroCFTA.SourceCurrentSelectedFirstChildKnown
