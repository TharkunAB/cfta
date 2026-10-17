import MicroCFTA.SourceMergedComparisonHistory
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.ComparisonHistoryIntegration
open InternedConstructorTemplates InternedProbeProvenance
open SourceMergedComparisonHistory
private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 9 true [
    .binder true (.node [.mk 0 true [.var 0], .mk 1 true []]),
    .node [.mk 1 true []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def recursive : Value Nat Bool := (children root).getD 0 .empty
private def narrow : Value Nat Bool := (children root).getD 1 .empty
private def observed := MergedFreshOrdinaryComparison.check (fun guard => guard) 4 [] recursive narrow heap
private def after := observed.state
private def limit := maximumDepth (InternedRecordCoherence.nodeInventory heap) + 1

private theorem constructed : built = .done root heap := by cbv
private theorem child_list : children root = [recursive, narrow] := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
private theorem inputs : Available heap recursive ∧ Available heap narrow := by
  have parent := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  exact ⟨parent.children recursive (by rw [child_list]; exact List.mem_cons_self),
    parent.children narrow (by rw [child_list]; exact List.mem_cons_of_mem _ List.mem_cons_self)⟩
private theorem closed : recursive.free = [] ∧ narrow.free = [] := by cbv
private theorem bounded : InternedMuDepthInventory.Bounded heap limit :=
  InternedMuDepthInventory.initial_bounded heap semantic.ready.semantic.1.normal.facts
private theorem first_done : MergedFreshOrdinaryComparison.check (fun guard => guard) 4 [] recursive narrow heap =
    .done true after := by cbv
private theorem recorded : Recorded limit heap after :=
  check_recorded limit (fun guard => guard) 4 [] recursive narrow heap semantic bounded
    inputs.1 inputs.2 closed.1 closed.2 true after first_done

/-- A source-built productive Mu comparison records actual unfolding and both new supplies. -/
theorem constructed_allocating :
    built = .done root heap ∧
    (match recursive with | .mu .. => True | _ => False) ∧
    MergedFreshOrdinaryComparison.check (fun guard => guard) 4 [] recursive narrow heap = .done true after ∧
    heap.nodes.next < after.nodes.next ∧ heap.edges.next < after.edges.next ∧
    Recorded limit heap after ∧ SourceCurrentAllocatedUnfoldHistory.History heap after := by
  exact ⟨constructed, by cbv, first_done, by cbv, by cbv, recorded, recorded.history⟩

/-- The second actual comparison starts at the first full return and retains that exact warm heap. -/
theorem constructed_warm :
    MergedFreshOrdinaryComparison.check (fun guard => guard) 4 [] recursive narrow heap = .done true after ∧
    MergedFreshOrdinaryComparison.check (fun guard => guard) 4 [] recursive narrow after = .done true after ∧
    Recorded limit heap after ∧ Recorded limit after after ∧
    SourceCurrentAllocatedUnfoldHistory.History heap after := by
  have warm : MergedFreshOrdinaryComparison.check (fun guard => guard) 4 [] recursive narrow after =
      .done true after := by cbv
  have retained := check_recorded limit (fun guard => guard) 4 [] recursive narrow after
    recorded.effect.2 recorded.bounded (recorded.effect.1.available recursive inputs.1)
    (recorded.effect.1.available narrow inputs.2) closed.1 closed.2 true after warm
  exact ⟨first_done, warm, recorded, retained, (recorded.trans retained).history⟩

end MicroCFTA.ComparisonHistoryIntegration

#print axioms MicroCFTA.ComparisonHistoryIntegration.constructed_allocating
#check @MicroCFTA.ComparisonHistoryIntegration.constructed_allocating
#print axioms MicroCFTA.ComparisonHistoryIntegration.constructed_warm
#check @MicroCFTA.ComparisonHistoryIntegration.constructed_warm
