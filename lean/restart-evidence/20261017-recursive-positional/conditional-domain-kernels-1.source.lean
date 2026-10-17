import MicroCFTA.SourceCurrentAllocatedPartialConditionalDomain

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.ConditionalDomainKernels
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialConditionalDomain
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State

private def rawEdge (identity : Nat) (guard : Guard) (children : List (Value Symbol Guard)) : Edge :=
  ⟨⟨identity, ⟨("s", .top), children.map Value.referenceOf, guard⟩⟩, children⟩
private def badGuard : Guard := ⟨none, .top⟩
private def badOwner : EdgeRequest := ⟨.live none [], rawEdge 0 badGuard [.empty]⟩
private def badResult : Edge := rawEdge 2 badGuard [.reference (.interned 0)]
private def plain : Edge := rawEdge 1 SourceEqualityConstraintConstructors.top []
private def plainOwner : EdgeRequest := ⟨.live none [], plain⟩
private def before (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) : Caller width :=
  { SourceCurrentAllocatedPartialState.initial checked merge fourth with
    edgeResults := ⟨put (put (fun _ => none) badOwner.key 0) plainOwner.key 1,
      put (put (fun _ => none) 0 ⟨badOwner, .evaluating⟩) 1 ⟨plainOwner, .returned plain⟩, 2⟩ }
private def finished (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) : Caller width :=
  finishEdge 0 badResult (before checked merge fourth)

private theorem bad_nonempty : ¬ OwnEmpty badOwner.value := by
  simp [OwnEmpty, badOwner, rawEdge, badGuard, SourceCompactGuards.sourceEqualities,
    SourceCompactGuards.positiveNormalized]
private theorem plain_empty : OwnEmpty plainOwner.value := by
  rfl
private theorem running (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    (before checked merge fourth).edgeResults.cells 0 = some ⟨badOwner, .evaluating⟩ := rfl
private theorem earlier_stored (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    Stored (before checked merge fourth) := by
  intro handle owner result found
  by_cases one : handle = 1
  · subst handle
    have same := Option.some.inj found
    cases same
    exact fun _ => Or.inl rfl
  · by_cases zero : handle = 0
    · subst handle
      simp [before, put] at found
    · simp [before, put, one, zero] at found

/-- A literal nonplain finish keeps the conditional store but violates the old universal shape law. -/
theorem mixed_finish (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    Stored (finished checked merge fourth) ∧
      ¬ SourceCurrentAllocatedPartialReturnedDomain.Stored (finished checked merge fourth) := by
  have retained := (earlier_stored checked merge fourth).finishEdge badResult (running checked merge fourth)
    (fun emptyOwn => (bad_nonempty emptyOwn).elim)
  refine ⟨retained, ?_⟩
  intro old
  have returned := finishEdge_returned 0 badOwner badResult (before checked merge fourth) (running checked merge fourth)
  have shape := old 0 badOwner badResult returned
  simp [SourceCurrentAllocatedPartialReturnedDomain.Shape, badOwner, badResult, rawEdge,
    EqualityLeafProjectionRuntimeEmpty.erase] at shape

/-- The unrelated nonplain finish preserves a literal warm plain hit and its owner-derived shape. -/
theorem mixed_warm_shape
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver (finished checked merge fourth))
    (coherent : InternedRecordCoherence.Coherent checked.native.machine.heap)
    (resident : InternedEdgeResidency.EdgeResident checked.native.machine.heap plain) :
    beginEdge plainOwner (finished checked merge fourth) = (1, .ready plain, finished checked merge fourth) ∧
      SourceCurrentAllocatedPartialReturnedDomain.Shape plain plain := by
  have hit := beginEdge_ready plainOwner plainOwner (finished checked merge fourth) 1 plain rfl rfl
  have certified := edge_ready_shape formulas solver plainOwner (finished checked merge fourth)
    (finished checked merge fourth) 1 plain sound coherent resident plain_empty
    (mixed_finish checked merge fourth).1 hit
  exact ⟨hit, certified.2⟩

end MicroCFTA.ConditionalDomainKernels

#print axioms MicroCFTA.ConditionalDomainKernels.mixed_finish
#check @MicroCFTA.ConditionalDomainKernels.mixed_finish
#print axioms MicroCFTA.ConditionalDomainKernels.mixed_warm_shape
#check @MicroCFTA.ConditionalDomainKernels.mixed_warm_shape
