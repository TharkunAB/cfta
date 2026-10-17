import MicroCFTA.SourceMergedSelectionMass
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.SelectionMassKernels
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceMergedComparisonMass (Resources)
open SourceMergedSelectionMass (selectionBound)
local notation "V" => Value Nat Bool
local notation "H" => State Nat Bool
private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 9 true [
    .binder true (.node [.mk 0 true [.var 0], .mk 1 true []]),
    .node [.mk 1 true []],
    .union [.node [.mk 1 true []], .node [.mk 2 true []]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : V := match built with | .done value _ => value | .pending .. => .empty
private def heap : H := built.state
private def recursive : V := (children root).getD 0 .empty
private def narrow : V := (children root).getD 1 .empty
private def alternatives : V := (children root).getD 2 .empty
private def inputs := [recursive, narrow, alternatives]
private def observed := SourceMergedSelection.select (fun guard => guard) 1 inputs heap
private def after : H := observed.state
private def bound := InternedValueMassHeap.initialBound heap

private theorem constructed : built = .done root heap := by cbv
private theorem child_list : children root = inputs := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
private theorem available : Values heap inputs := by
  have parent := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  intro value member
  exact parent.children value (by simpa only [child_list] using member)
private theorem closed : MergedColdReaderClosedInputs.ClosedValues inputs := by
  intro value member
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> cbv
private theorem stored : InternedValueMassHeap.Stored bound heap :=
  InternedValueMassHeap.initial heap semantic.ready.semantic.1.normal.facts
private theorem first_done : SourceMergedSelection.select (fun guard => guard) 1 inputs heap =
    .done [recursive, alternatives] after := by cbv
private theorem effects : SourceMergedComparisonEffects.Effect heap after := by
  obtain ⟨retained, final, actual, returned⟩ :=
    (SourceMergedComparisonEffects.bind_done _ _ [recursive, alternatives] after).mp first_done
  have equal : final = after := (MergedSourceComparison.Result.done.inj returned).2
  subst after
  exact SourceMergedSelection.retain_effect (fun guard => guard) 1
    (inputs.filter MergedPhysicalGroupColumns.closedMu) inputs heap semantic
    (fun value member => available value (List.mem_filter.mp member).1)
    (fun value member => closed value (List.mem_filter.mp member).1) available closed retained final actual
private theorem first_bounds : Resources (selectionBound 1 inputs.length bound) heap after :=
  SourceMergedSelectionMass.select_bound (fun guard => guard) 1 inputs heap bound semantic stored available closed
    [recursive, alternatives] after first_done

/-- An actual closed Mu and union selection allocates its unfolding and derives both supply bounds. -/
theorem cold_recursive_union :
    built = .done root heap ∧
    (match recursive with | .mu .. => True | _ => False) ∧
    (match alternatives with | .union .. => True | _ => False) ∧
    SourceMergedSelection.select (fun guard => guard) 1 inputs heap = .done [recursive, alternatives] after ∧
    heap.nodes.next < after.nodes.next ∧ heap.edges.next < after.edges.next ∧
    Resources (selectionBound 1 inputs.length bound) heap after := by
  exact ⟨constructed, by cbv, by cbv, first_done, by cbv, by cbv, first_bounds⟩

/-- A second actual selection reuses the first complete heap and its derived causal mass store. -/
theorem warm_replay :
    SourceMergedSelection.select (fun guard => guard) 1 inputs heap = .done [recursive, alternatives] after ∧
    Resources (selectionBound 1 inputs.length bound) heap after ∧
    SourceMergedSelection.select (fun guard => guard) 1 inputs after = .done [recursive, alternatives] after ∧
    Resources (selectionBound 1 inputs.length (selectionBound 1 inputs.length bound)) after after := by
  have actual : SourceMergedSelection.select (fun guard => guard) 1 inputs after =
      .done [recursive, alternatives] after := by cbv
  exact ⟨first_done, first_bounds, actual,
    SourceMergedSelectionMass.select_bound (fun guard => guard) 1 inputs after _ effects.2 first_bounds.stored
      (fun value member => effects.1.available value (available value member)) closed [recursive, alternatives] after actual⟩

end MicroCFTA.SelectionMassKernels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.SelectionMassKernels.cold_recursive_union
#check @MicroCFTA.SelectionMassKernels.cold_recursive_union
#print axioms MicroCFTA.SelectionMassKernels.warm_replay
#check @MicroCFTA.SelectionMassKernels.warm_replay
