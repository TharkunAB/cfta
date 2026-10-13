import MicroCFTA.InternedNestedProbeCostBoundary
import MicroCFTA.InternedFlatProbeHeap

/-!
# A closed source run can store the nested probe-cost counterexample

Two enclosing binders create the captured source sentinels during their
actual probes. A discarded enclosing edge makes its output empty. The
completed recursive cache still retains the record with the extra inner
binder cost. The final closed result completes and is empty.
-/
namespace MicroCFTA.InternedClosedProbeCostBoundary
open InternedConstructorTemplates InternedNestedConstruction InternedFreeOccurrenceRank
open InternedBinderProtocol (Reference NodeRef)
open InternedNestedProbeCostBoundary (observations)

/-- Discarding the inner result gives both enclosing probes depth zero. -/
def expression : Syntax Nat Unit := .binder true (.binder true
  (.node [.mk 3 () [.binder false InternedNestedProbeCostBoundary.body, .empty]]))

/-- Execute the closed source expression from empty independent caches. -/
def result := build expression [] (empty : State Nat Unit)

/-- Select the actual canonical slot issued during the ordinary enclosing probe. -/
def selected : Option (Value Nat Unit) := do
  let key ← result.state.nodes.issued 19
  result.state.nodeRecords key

/-- Observe the complete stored payload without reconstructing its body. -/
def selectedCosts := selected.bind fun value => observations (.done value result.state)

/-- The closed source cache contains the same uncovered external costs. -/
theorem actual_costs : selectedCosts = some (19,
    [(.depth, 1), (.uninterned 0, 1), (.interned 19, 1)],
    [(.depth, 0), (.uninterned 0, 0)], [(.depth, 0), (.uninterned 0, 0)]) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 20000000 in cbv

/-- The original flat-callback cost invariant is false as an unrestricted closed-cache invariant. -/
theorem not_flat_probe_heap : ¬ InternedFlatProbeHeap.Heap result.state := by
  intro heap
  have actual := actual_costs
  cases issued : result.state.nodes.issued 19 with
  | none => simp [selectedCosts, selected, issued] at actual
  | some key =>
      cases stored : result.state.nodeRecords key with
      | none => simp [selectedCosts, selected, issued, stored] at actual
      | some value =>
          have related := heap key value stored
          cases value with
          | empty | reference | node | union => simp [selectedCosts, selected, issued, stored, observations] at actual
          | mu entry body depth ordinary =>
              simp [selectedCosts, selected, issued, stored, observations] at actual
              have member : (Reference.depth, 2) ∈ costs (.mu entry body depth ordinary) := by
                rw [costs]
                apply List.mem_map.mpr
                refine ⟨(.depth, 1), List.mem_filter.mpr ⟨?_, by simp⟩, rfl⟩
                rw [actual.2.1]
                simp
              obtain ⟨prior, count, covered⟩ := related .depth 2 member
              have previous : prior = 1 := by omega
              rw [previous, actual.2.2.1, actual.2.2.2] at covered
              simp at covered

/-- No external literal reference is needed to construct this source counterexample. -/
theorem expression_scoped : Scoped 0 expression := by
  simp [expression, InternedNestedProbeCostBoundary.body, Scoped, EdgesScoped, ManyScoped]

/-- Observe source completion without exposing implementation counters. -/
def returnedReference : Outcome Symbol Guard (Value Symbol Guard) → Option NodeRef
  | .done value _ => some value.referenceOf
  | .pending .. => none

/-- The counterexample completes with EmptyNode; it does not exhibit source divergence. -/
theorem complete_empty : returnedReference result = some .empty := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 20000000 in cbv

end MicroCFTA.InternedClosedProbeCostBoundary
