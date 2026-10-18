import MicroCFTA.SourceCurrentOuterEdgeIdle
import MicroCFTA.SourceCurrentOuterExecutionAncestry

/-!
# Edge idle at literal outer phase entries

Completed earlier workers preserve edge idle. The literal prefix steps
enter descendants only after the edge owner has finished. No semantic,
resource or successful-enclosing-call premise is required. A terminal
failed Parent body can retain an evaluating edge and is not a phase entry
in this prefix relation.
-/
namespace MicroCFTA.SourceCurrentOuterEdgeIdleReached
open InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterEdgeIdle (EdgeIdle Safe)
open SourceCurrentOuterExecutionAncestry (Step Reached)
open SourceCurrentOuterActiveAncestry (caller)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)]

private theorem edge_done
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done result after)
    (idle : EdgeIdle before) : EdgeIdle after := by
  have safe := SourceCurrentOuterEdgeIdle.edge_call fuel g s r e p h m c n budget request before idle
  rw [actual] at safe
  exact safe

private theorem descendants_done
    (actual : descendants fuel g s r e p h m c n budget inherited value before = .done result after)
    (idle : EdgeIdle before) : EdgeIdle after := by
  have safe := SourceCurrentOuterEdgeIdle.descendant_pass fuel g s r e p h m c n budget inherited value before idle
  rw [actual] at safe
  exact safe

private theorem node_done
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done result after)
    (idle : EdgeIdle before) : EdgeIdle after := by
  have safe := SourceCurrentOuterEdgeIdle.node_call fuel g s r e p h m c n budget request before idle
  rw [actual] at safe
  exact safe

/-- Every literal prefix step preserves edge idle at its exact next phase entry. -/
theorem step (actual : Step g s r e p h m c n budget first last)
    (idle : EdgeIdle (caller first)) : EdgeIdle (caller last) := by
  cases actual with
  | node_evaluate started =>
      rename_i request before handle running original fuel
      have same := (beginNode_components request before).2.2.2
      rw [started] at same
      change EdgeIdle running
      unfold EdgeIdle
      rw [same]
      exact idle
  | body_rows => exact idle
  | rows_edge actual => exact edge_done actual idle
  | rows_tail edge children => exact descendants_done children (edge_done edge idle)
  | descendants_children => exact idle
  | children_walk => exact idle
  | walk_head => exact idle
  | walk_tail actual => exact node_done actual idle

/-- An actual unfinished outer prefix keeps every reached phase entry edge-idle. -/
theorem reached (actual : Reached g s r e p h m c n budget first last)
    (idle : EdgeIdle (caller first)) : EdgeIdle (caller last) := by
  induction actual with
  | refl => exact idle
  | snoc earlier last ih => exact step last ih

end MicroCFTA.SourceCurrentOuterEdgeIdleReached
