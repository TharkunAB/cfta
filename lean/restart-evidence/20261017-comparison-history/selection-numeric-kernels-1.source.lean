import MicroCFTA.SourceMergedSelectionNumeric
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.SelectionNumericIntegration
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceMergedComparisonMass (Resources)
open SourceMergedSelectionMass (selectionBound)
open SourceMergedComparisonNumeric (comparisonFuel)
open SourceCurrentAllocatedUnfoldHistory (Fits heapBound)
private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 9 true [
    .binder true (.node [.mk 0 true [.var 0], .mk 1 true []]),
    .node [.mk 1 true []],
    .union [.binder true (.node [.mk 0 true [.var 0], .mk 1 true []]), .node [.mk 2 true []]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def recursive : Value Nat Bool := (children root).getD 0 .empty
private def narrow : Value Nat Bool := (children root).getD 1 .empty
private def alternatives : Value Nat Bool := (children root).getD 2 .empty
private def inputs := [recursive, narrow, alternatives]
private def observed := SourceMergedSelection.select (fun guard => guard) 4 inputs heap
private def after := observed.state
private def mass := InternedValueMassHeap.initialBound heap
private def fuel := comparisonFuel heap.nodes.next heap.edges.next mass
private def ceiling := heapBound heap.nodes.next heap.edges.next mass

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
private theorem stored : InternedValueMassHeap.Stored mass heap :=
  InternedValueMassHeap.initial heap semantic.ready.semantic.1.normal.facts
private theorem literal : SourceMergedSelection.select (fun guard => guard) 4 inputs heap =
    .done [recursive, alternatives] after := by cbv

private theorem computed :
    SourceMergedSelection.select (fun guard => guard) fuel inputs heap = .done [recursive, alternatives] after ∧
    SourceMergedComparisonEffects.Effect heap after ∧ Fits ceiling after ∧
    Resources (selectionBound fuel inputs.length mass) heap after ∧
    ∀ extra, SourceMergedSelection.select (fun guard => guard) (fuel + extra) inputs heap = .done [recursive, alternatives] after := by
  obtain ⟨result, final, done, effect, fits, resources, stable⟩ :=
    SourceMergedSelectionNumeric.select_complete (fun guard => guard) inputs heap mass semantic stored available closed
  have exactReturn := SourceMergedSelectionNumeric.select_replay heap mass semantic stored 4 fuel
    (fun guard => guard) (Nat.le_refl _) inputs heap semantic available closed (.refl heap)
    [recursive, alternatives] after literal
  obtain ⟨rfl, rfl⟩ := MergedSourceComparison.Result.done.inj (done.symm.trans exactReturn)
  exact ⟨done, effect, fits, resources, stable⟩

/-- Own initial facts construct the full allocating Mu/union selection at symbolic computed fuel. -/
theorem initial_computed_selection :
    built = .done root heap ∧
    (match recursive with | .mu .. => True | _ => False) ∧
    (match alternatives with | .union .. => True | _ => False) ∧
    heap.nodes.next < after.nodes.next ∧ heap.edges.next < after.edges.next ∧
    SourceMergedSelection.select (fun guard => guard) fuel inputs heap = .done [recursive, alternatives] after ∧
    Fits ceiling after ∧ Resources (selectionBound fuel inputs.length mass) heap after ∧
    ∀ extra, SourceMergedSelection.select (fun guard => guard) (fuel + extra) inputs heap = .done [recursive, alternatives] after := by
  exact ⟨constructed, by cbv, by cbv, by cbv, by cbv, computed.1, computed.2.2.1, computed.2.2.2⟩

/-- The warm selection uses the same original fuel and exact first heap with no later-entry premise. -/
theorem same_origin_warm :
    SourceMergedSelection.select (fun guard => guard) fuel inputs heap = .done [recursive, alternatives] after ∧
    SourceMergedSelection.select (fun guard => guard) fuel inputs after = .done [recursive, alternatives] after ∧
    Fits ceiling after ∧ Resources (selectionBound fuel inputs.length ceiling) after after ∧
    SourceCurrentAllocatedUnfoldHistory.History heap after := by
  have recorded := SourceMergedSelectionNumeric.select_recorded mass (fun guard => guard) fuel inputs heap semantic
    (InternedValueMassBinderDepth.stored_bounded heap mass stored) available closed [recursive, alternatives] after computed.1
  have warmLiteral : SourceMergedSelection.select (fun guard => guard) 4 inputs after =
      .done [recursive, alternatives] after := by cbv
  have warm := SourceMergedSelectionNumeric.select_replay heap mass semantic stored 4 fuel (fun guard => guard)
    (Nat.le_refl _) inputs after recorded.effect.2
    (fun value member => recorded.effect.1.available value (available value member)) closed recorded.history
    [recursive, alternatives] after warmLiteral
  have resources := SourceMergedSelectionMass.select_bound (fun guard => guard) fuel inputs after ceiling
    recorded.effect.2 computed.2.2.1.stored
    (fun value member => recorded.effect.1.available value (available value member)) closed [recursive, alternatives] after warm
  exact ⟨computed.1, warm, computed.2.2.1, resources, recorded.history⟩

end MicroCFTA.SelectionNumericIntegration

#print axioms MicroCFTA.SelectionNumericIntegration.initial_computed_selection
#check @MicroCFTA.SelectionNumericIntegration.initial_computed_selection
#print axioms MicroCFTA.SelectionNumericIntegration.same_origin_warm
#check @MicroCFTA.SelectionNumericIntegration.same_origin_warm
