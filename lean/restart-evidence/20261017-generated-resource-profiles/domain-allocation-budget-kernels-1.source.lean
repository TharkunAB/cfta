import MicroCFTA.InternedFreshOrdinaryAllocationBudget
import MicroCFTA.InternedFreshOrdinaryReplay

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace MicroCFTA.FreshAllocationBudgetIntegration
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedFreshOrdinaryAllocationBudget

private def fixture : Syntax Nat Bool :=
  .binder false (.node [.mk 7 false [.var 0,
    .binder false (.union [.var 0, .node [.mk 8 true [.var 1]]])]])

/-- A nested captured binder executes both probes and fresh bodies within the original budget. -/
theorem nested_callbacks :
    let actual := build fixture [] empty
    (match actual with | .done _ _ => true | .pending _ _ => false) = true ∧
      actual.state.nodes.next = 19 ∧ actual.state.edges.next = 6 ∧
      nodeBudget fixture = 37 ∧ edgeBudget fixture = 12 ∧
      actual.state.nodes.next ≤ nodeBudget fixture ∧ actual.state.edges.next ≤ edgeBudget fixture := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, ?_⟩
  exact build_bound fixture [] empty

private def reservedKey : InternedBinderProtocol.NodeKey :=
  muKey (Value.reference .depth : Value Nat Bool) (.reference (.uninterned 0))

private def reservedHeap : State Nat Bool :=
  {empty with nodes := (Cache.intern (empty (Symbol := Nat) (Guard := Bool)).nodes reservedKey).2}

/-- A literal previously reserved owner causes pending readback after its exact probes without new allocation. -/
theorem reserved_pending :
    build (.binder false (.var 0)) [] reservedHeap = .pending reservedKey reservedHeap ∧
      reservedHeap.nodes.next = 1 ∧ reservedHeap.edges.next = 0 ∧
      (build (.binder false (.var 0)) [] reservedHeap).state.nodes.next ≤
        reservedHeap.nodes.next + nodeBudget (.binder false (.var 0)) ∧
      (build (.binder false (.var 0)) [] reservedHeap).state.edges.next ≤
        reservedHeap.edges.next + edgeBudget (.binder false (.var 0)) := by
  exact ⟨rfl, rfl, rfl, build_bound (.binder false (.var 0)) [] reservedHeap⟩

/-- The actual first nested return supplies exact replay and the summed initial list budget. -/
theorem repeated_nested :
    ∃ value after,
      build fixture [] empty = .done value after ∧
      build fixture [] after = .done value after ∧
      buildMany [fixture, fixture] [] empty = .done [value, value] after ∧
      after.nodes.next = 19 ∧ after.edges.next = 6 ∧
      after.nodes.next ≤ manyNodes [fixture, fixture] ∧ after.edges.next ≤ manyEdges [fixture, fixture] := by
  have finished : (match build fixture [] empty with | .done _ _ => true | .pending _ _ => false) = true := by decide
  cases actual : build fixture [] empty with
  | pending key after => simp only [actual, Bool.false_eq_true] at finished
  | done value after =>
      have repeated := InternedFreshOrdinaryReplay.empty_replay fixture value after actual
      have serial : buildMany [fixture, fixture] [] empty = .done [value, value] after := by
        simp only [buildMany, actual, repeated, Outcome.bind]
      have budget := buildMany_bound [fixture, fixture] [] (empty (Symbol := Nat) (Guard := Bool))
      rw [serial] at budget
      have counts := nested_callbacks
      change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at counts
      rw [actual] at counts
      exact ⟨value, after, actual, repeated, serial, counts.2.1, counts.2.2.1, budget⟩

end MicroCFTA.FreshAllocationBudgetIntegration

#print axioms MicroCFTA.FreshAllocationBudgetIntegration.nested_callbacks
#check @MicroCFTA.FreshAllocationBudgetIntegration.nested_callbacks
#print axioms MicroCFTA.FreshAllocationBudgetIntegration.reserved_pending
#check @MicroCFTA.FreshAllocationBudgetIntegration.reserved_pending
#print axioms MicroCFTA.FreshAllocationBudgetIntegration.repeated_nested
#check @MicroCFTA.FreshAllocationBudgetIntegration.repeated_nested
