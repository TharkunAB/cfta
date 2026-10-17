import MicroCFTA.SourceCurrentAllocatedPartialConditionalFrames

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.ConditionalActiveKernels
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialConditionalActive
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State

private def capEdge : EdgeValue Symbol Guard := ⟨⟨0, ⟨("cap", .top), [], ⟨none, .top⟩⟩⟩, []⟩
private def capValue : Node := .node ⟨0, .node []⟩ [capEdge] 0 []
private def capOwner : NodeRequest := ⟨.live 0 [], capValue⟩
private def emptyOwner : NodeRequest := ⟨.live 0 [], .empty⟩
private def before (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) : Caller width :=
  { SourceCurrentAllocatedPartialState.initial checked merge fourth with
    nodeResults := ⟨put (fun _ => none) capOwner.key 0, put (fun _ => none) 0 ⟨capOwner, .evaluating⟩, 1⟩ }
private def after (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) : Caller width :=
  finishNode 1 .empty (beginNode emptyOwner (before checked merge fourth)).2.2

private theorem cap_not_region : ¬ SourceEqualityPartialPlainRegion.Region capValue := by
  intro region
  cases region with
  | ordinary rows =>
      cases rows with
      | cons physical _ _ =>
          have own := SourceCurrentAllocatedPartialPlainInputs.own_empty _ physical
          change (none : Option (List (List SourceGuards.Path))) = some [] at own
          cases own

private theorem filtered (bound : Nat) (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    ActiveAbove bound (before checked merge fourth) := by
  constructor
  · intro handle owner found region
    by_cases zero : handle = 0
    · subst handle
      have same := Option.some.inj found
      cases same
      exact (cap_not_region region).elim
    · simp [before, put, zero] at found
  · intro handle owner found
    cases found

/-- A completed Empty request and erasure retain an arbitrarily high filtered ancestor bound. -/
theorem completed_mixed_prefix [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (budget bound : Nat) (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    ∃ actual : NodeCall budget emptyOwner (before checked merge fourth) .empty (after checked merge fourth),
      ∃ erased : Children budget .contradiction [capValue] (after checked merge fourth) [.empty] (after checked merge fourth),
        ActiveAbove bound (after checked merge fourth) ∧
        ¬ SourceCurrentAllocatedPartialActiveOrder.ActiveAbove
          (SourceCurrentAllocatedPartialActiveOrder.nodeRank capOwner) (before checked merge fourth) := by
  have started : beginNode emptyOwner (before checked merge fourth) =
      (1, .evaluate emptyOwner, (beginNode emptyOwner (before checked merge fourth)).2.2) := rfl
  let actual : NodeCall budget emptyOwner (before checked merge fourth) .empty (after checked merge fourth) :=
    .evaluate started .empty
  let erased : Children budget .contradiction [capValue] (after checked merge fourth) [.empty] (after checked merge fourth) :=
    .contradiction
  have first := SourceCurrentAllocatedPartialConditionalFrames.node_call actual (filtered bound checked merge fourth)
  have later := SourceCurrentAllocatedPartialConditionalFrames.children erased first
  refine ⟨actual, erased, later, ?_⟩
  intro old
  have impossible := old.nodes 0 capOwner (by simp) rfl
  exact (Nat.lt_irrefl _) impossible

end MicroCFTA.ConditionalActiveKernels

#print axioms MicroCFTA.ConditionalActiveKernels.completed_mixed_prefix
#check @MicroCFTA.ConditionalActiveKernels.completed_mixed_prefix
