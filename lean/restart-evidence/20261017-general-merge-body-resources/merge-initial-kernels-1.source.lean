import MicroCFTA.SourceCurrentMemoMergeNumeric
import MicroCFTA.InternedFreshOrdinaryCosts
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.InitialMergeIntegration
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph (Call Memo remember)
open SourceCurrentMemoMergeEffects (Effect Stored)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentMemoMergeNumeric (workFuel selectionFuel)

private def leaf (symbol : Nat) : InternedNestedConstruction.Syntax Nat Bool := .node [.mk symbol true []]
private def recursivePlan : InternedNestedConstruction.Syntax Nat Bool :=
  .binder true (.node [.mk 0 true [.var 0], .mk 1 true []])
private def ordinaryPlan : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 9 true [leaf 1], .mk 9 true [leaf 2], .mk 9 true [leaf 3], .mk 9 true [leaf 4], .mk 9 true [leaf 5]]
private def mixedPlan : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 9 true [recursivePlan], .mk 9 true [leaf 1], .mk 9 true [.union [recursivePlan, leaf 2]],
    .mk 9 true [leaf 3], .mk 9 true [leaf 4]]
private def built (plan : InternedNestedConstruction.Syntax Nat Bool) := InternedFreshOrdinaryConstruction.build plan [] empty
private def input (plan : InternedNestedConstruction.Syntax Nat Bool) : Value Nat Bool :=
  match built plan with | .done value _ => value | .pending .. => .empty
private def heap (plan : InternedNestedConstruction.Syntax Nat Bool) := (built plan).state
private def mass (plan : InternedNestedConstruction.Syntax Nat Bool) := InternedValueMassHeap.initialBound (heap plan)
private def ceiling (plan : InternedNestedConstruction.Syntax Nat Bool) :=
  workFuel (input plan) (heap plan).nodes.next (heap plan).edges.next (mass plan)
private def selection (plan : InternedNestedConstruction.Syntax Nat Bool) :=
  selectionFuel (input plan) (heap plan).nodes.next (heap plan).edges.next (mass plan)

private theorem constructed (plan : InternedNestedConstruction.Syntax Nat Bool) :
    built plan = .done (input plan) (heap plan) := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  simp only [built, input, heap, done, InternedNestedConstruction.Outcome.state]
private theorem semantic (plan : InternedNestedConstruction.Syntax Nat Bool) : SemanticReady (heap plan) :=
  SourceEqualityRequiredSemanticCache.constructed plan _ _ (constructed plan)
private theorem available (plan : InternedNestedConstruction.Syntax Nat Bool) : Available (heap plan) (input plan) :=
  (InternedFreshOrdinaryFacts.closed_verified plan).result _ _ (constructed plan)

private def Completed (plan : InternedNestedConstruction.Syntax Nat Bool) : Prop :=
  ∃ output after saved,
    Call id true (input plan) (heap plan) SourceCurrentMemoMergeGraph.empty output after saved ∧
    SourceCurrentMemoMergeWorker.call id true (ceiling plan) (selection plan)
      (input plan) (heap plan) SourceCurrentMemoMergeGraph.empty = .done output after saved ∧
    Effect (heap plan) after ∧ Stored after saved ∧ Available after output ∧ Fits (ceiling plan) after ∧
    ∀ workExtra selectionExtra, SourceCurrentMemoMergeWorker.call id true
      (ceiling plan + workExtra) (selection plan + selectionExtra)
      (input plan) (heap plan) SourceCurrentMemoMergeGraph.empty = .done output after saved
private theorem completed (plan : InternedNestedConstruction.Syntax Nat Bool) : Completed plan := by
  obtain ⟨output, after, saved, actual, done, effect, stored, result, _closed, fits, _small, stable⟩ :=
    SourceCurrentMemoMergeNumeric.complete id true (input plan) (heap plan) SourceCurrentMemoMergeGraph.empty (mass plan)
      (semantic plan) (InternedFreshOrdinaryCosts.closed_heap plan) (SourceCurrentMemoMergeEffects.stored_empty _)
      (available plan) (InternedValueMassHeap.initial _ (semantic plan).ready.semantic.1.normal.facts)
  exact ⟨output, after, saved, actual, done, effect, stored, result, fits, stable⟩

/-- An ordinary five-row group constructs its own complete initial-budget execution. -/
theorem ordinary_large :
    built ordinaryPlan = .done (input ordinaryPlan) (heap ordinaryPlan) ∧
    (MergedSourceGrouping.groups (InternedEdgeResidency.nodeEdges (input ordinaryPlan))).map List.length = [5] ∧
    Completed ordinaryPlan :=
  ⟨constructed ordinaryPlan, by cbv, completed ordinaryPlan⟩

/-- A five-row recursive group includes real Mu and union operands in its complete initial-budget execution. -/
theorem recursive_large :
    built mixedPlan = .done (input mixedPlan) (heap mixedPlan) ∧
    (MergedSourceGrouping.groups (InternedEdgeResidency.nodeEdges (input mixedPlan))).map List.length = [5] ∧
    Completed mixedPlan :=
  ⟨constructed mixedPlan, by cbv, completed mixedPlan⟩

/-- A productive Mu input uses the source height-zero boundary with computed initial fuels. -/
theorem recursive_boundary :
    built recursivePlan = .done (input recursivePlan) (heap recursivePlan) ∧
    MergedOrdinaryHeight.height (input recursivePlan) = 0 ∧ Completed recursivePlan :=
  ⟨constructed recursivePlan, by cbv, completed recursivePlan⟩

/-- A second computed call uses the exact heap and populated memo returned by the first call. -/
theorem cold_then_warm :
    ∃ output after saved,
      SourceCurrentMemoMergeWorker.call id true (ceiling mixedPlan) (selection mixedPlan)
        (input mixedPlan) (heap mixedPlan) SourceCurrentMemoMergeGraph.empty = .done output after saved ∧
      Fits (ceiling mixedPlan) after ∧
      SourceCurrentMemoMergeWorker.call id true
        (workFuel (input mixedPlan) after.nodes.next after.edges.next (ceiling mixedPlan))
        (selectionFuel (input mixedPlan) after.nodes.next after.edges.next (ceiling mixedPlan))
        (input mixedPlan) after saved = .done output after saved := by
  obtain ⟨output, after, saved, actual, done, effect, stored, result, fits, _stable⟩ := completed mixedPlan
  obtain ⟨entry, found, same⟩ := actual.present
  obtain ⟨warmOutput, warmAfter, warmMemo, warmActual, warmDone, _effects, _stored, _result, _closed, _fits, _small, _again⟩ :=
    SourceCurrentMemoMergeNumeric.complete id true (input mixedPlan) after saved (ceiling mixedPlan)
      effect.semantic effect.costs stored (effect.keeps.available _ (available mixedPlan)) fits.stored
  obtain ⟨sameHeap, sameMemo, sameOutput⟩ := warmActual.hit_unchanged entry found
  have returned : warmOutput = output := sameOutput.trans same.symm
  rw [sameHeap, sameMemo, returned] at warmDone
  exact ⟨output, after, saved, done, fits, warmDone⟩

end MicroCFTA.InitialMergeIntegration

#print axioms MicroCFTA.InitialMergeIntegration.ordinary_large
#check @MicroCFTA.InitialMergeIntegration.ordinary_large
#print axioms MicroCFTA.InitialMergeIntegration.recursive_large
#check @MicroCFTA.InitialMergeIntegration.recursive_large
#print axioms MicroCFTA.InitialMergeIntegration.recursive_boundary
#check @MicroCFTA.InitialMergeIntegration.recursive_boundary
#print axioms MicroCFTA.InitialMergeIntegration.cold_then_warm
#check @MicroCFTA.InitialMergeIntegration.cold_then_warm
