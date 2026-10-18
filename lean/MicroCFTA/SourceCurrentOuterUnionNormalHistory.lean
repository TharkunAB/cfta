import MicroCFTA.SourceCurrentUnionNormalOuter
import MicroCFTA.SourceCurrentOuterExecutionAncestry

/-!
# Union normality at actual unfinished outer prefixes

An actual prefix keeps the exact heap after each completed earlier call.
Initial union normality reaches its unfinished endpoint. Running that
endpoint also preserves normality at every stopping outcome. No future
whole-call return or physical Good certificate is an input.
-/
namespace MicroCFTA.SourceCurrentOuterUnionNormalHistory
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "run" => SourceCurrentOuterActiveAncestry.run
private theorem erase (actual : Outcome A width) :
    (actual.bind (fun _ after => .done () after)).state = actual.state := by
  cases actual <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

private theorem step {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Step g s r e p h m c n budget first last)
    (normal : UnionNormal (caller first).checked.native.machine.heap) :
    UnionNormal (caller last).checked.native.machine.heap := by
  cases actual with
  | node_evaluate started =>
    rename_i request before handle running original fuel
    have same := (beginNode_components request before).1
    rw [started] at same
    change UnionNormal running.checked.native.machine.heap
    rw [same]
    exact normal
  | body_rows | children_walk | walk_head | descendants_children => exact normal
  | rows_edge actual =>
    rename_i fuel inherited original before narrowed middle rest
    have kept := SourceCurrentUnionNormalOuter.edge_call fuel g s r e p h m c n budget ⟨inherited,original⟩ before normal
    rw [actual] at kept
    exact kept
  | rows_tail first last =>
    rename_i fuel inherited original before narrowed current result after rest
    have middle := SourceCurrentUnionNormalOuter.edge_call fuel g s r e p h m c n budget ⟨inherited,original⟩ before normal
    rw [first] at middle
    have final := SourceCurrentUnionNormalOuter.descendant_pass fuel g s r e p h m c n budget inherited narrowed current middle
    rw [last] at final
    exact final
  | walk_tail actual =>
    rename_i fuel before combined index value result middle rest
    have kept := SourceCurrentUnionNormalOuter.node_call fuel g s r e p h m c n budget
      ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1,value⟩
      (SourceCurrentAllocatedPartialGraph.descend before combined index).2 normal
    rw [actual] at kept
    exact kept

/-- Every literal unfinished outer prefix preserves initial union normality. -/
theorem reached {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Reached g s r e p h m c n budget first last)
    (normal : UnionNormal (caller first).checked.native.machine.heap) :
    UnionNormal (caller last).checked.native.machine.heap := by
  induction actual with
  | refl => exact normal
  | snoc earlier last ih => exact step last ih

private theorem phase (g s r e p h m c n budget : Nat) (last : Phase width)
    (normal : UnionNormal (caller last).checked.native.machine.heap) :
    UnionNormal (run g s r e p h m c n budget last).state.checked.native.machine.heap := by
  cases last with
  | node fuel request before =>
    simpa only [SourceCurrentOuterActiveAncestry.run,erase] using SourceCurrentUnionNormalOuter.node_call fuel g s r e p h m c n budget request before normal
  | body fuel request before =>
    simpa only [SourceCurrentOuterActiveAncestry.run,erase] using SourceCurrentUnionNormalOuter.node_body fuel g s r e p h m c n budget request before normal
  | rows fuel inherited values before =>
    simpa only [SourceCurrentOuterActiveAncestry.run,erase] using SourceCurrentUnionNormalOuter.row_pass fuel g s r e p h m c n budget inherited values before normal
  | descendants fuel inherited value before =>
    simpa only [SourceCurrentOuterActiveAncestry.run,erase] using SourceCurrentUnionNormalOuter.descendant_pass fuel g s r e p h m c n budget inherited value before normal
  | children fuel inherited values before =>
    simpa only [SourceCurrentOuterActiveAncestry.run,erase] using SourceCurrentUnionNormalOuter.child_pass fuel g s r e p h m c n budget inherited values before normal
  | walk fuel inherited index values before =>
    simpa only [SourceCurrentOuterActiveAncestry.run,erase] using SourceCurrentUnionNormalOuter.indexed_walk fuel g s r e p h m c n budget inherited index values before normal

/-- Every stopping outcome after an actual prefix retains initial union normality. -/
theorem stopping {g s r e p h m c n budget : Nat} {first last : Phase width}
    (actual : Reached g s r e p h m c n budget first last)
    (normal : UnionNormal (caller first).checked.native.machine.heap) :
    UnionNormal (run g s r e p h m c n budget last).state.checked.native.machine.heap :=
  phase g s r e p h m c n budget last (reached actual normal)

/-- Literal closed construction supplies normality for the reached heap and its stopping outcome. -/
theorem constructed {g s r e p h m c n budget : Nat} {first last : Phase width}
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (entry : (caller first).checked.native.machine.heap =
      (InternedFreshOrdinaryConstruction.build expression [] empty).state)
    (actual : Reached g s r e p h m c n budget first last) :
    UnionNormal (caller last).checked.native.machine.heap ∧
    UnionNormal (run g s r e p h m c n budget last).state.checked.native.machine.heap := by
  have normal : UnionNormal (caller first).checked.native.machine.heap := by
    rw [entry]
    exact SourceCurrentRequiredUnionNormal.source expression
  exact ⟨reached actual normal,stopping actual normal⟩
end MicroCFTA.SourceCurrentOuterUnionNormalHistory
