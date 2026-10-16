import MicroCFTA.SourceCurrentHereditaryRequiredMerge
import MicroCFTA.SourceCurrentMemoMergeCompletion
import MicroCFTA.SourceEqualityRequiredComplete
import MicroCFTA.InternedFreshOrdinaryCosts

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.HereditaryRequiredMergeRequiredKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryConstruction
open SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceCurrentMemoMergeGraph
variable {Symbol Guard : Type}

/-- Allowed original syntax constructs its own Required and memo-aware Merge graphs. -/
theorem constructed_required_then_merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed valid expression) (needed : SourceEqualityNeeded.Needed) :
    ∃ original before required middle result after memo,
      InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done original before ∧
      RequireNode needed original before required middle ∧
      Call clear top required middle SourceCurrentMemoMergeGraph.empty result after memo ∧
      MuStored valid middle ∧ Annotated valid required ∧
      SourceCurrentHereditaryMerge.Stored valid memo ∧ Annotated valid result := by
  obtain ⟨original, before, built, stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed valid expression allowed
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression original before built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result original before built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression original before built
  have costs : InternedFreshOrdinaryCostHeap.Heap before := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  obtain ⟨required, middle, actual, _keeps, _available, _closed⟩ := SourceEqualityRequiredComplete.complete needed original before semantic.ready available closed
  obtain ⟨middleStored, requiredAnnotated⟩ := SourceCurrentHereditaryRequiredMerge.node valid actual semantic costs available closed stored annotated
  have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) actual semantic costs (by intro _ _ _; trivial) available
  obtain ⟨result, after, memo, merge, _effects⟩ := SourceCurrentMemoMergeCompletion.call_complete clear top required middle
    SourceCurrentMemoMergeGraph.empty effects.2.1 effects.2.2.1 (SourceCurrentMemoMergeEffects.stored_empty middle) effects.2.2.2.2
  obtain ⟨_, _, mergeStored, resultAnnotated⟩ := SourceCurrentHereditaryMerge.cold valid topValid merge effects.2.1 effects.2.2.1 effects.2.2.2.2 requiredAnnotated
  exact ⟨original, before, required, middle, result, after, memo, built, actual, merge, middleStored, requiredAnnotated, mergeStored, resultAnnotated⟩

/-- The raw self binder uses an actual recursive head before the selected Required return. -/
theorem raw_self_selected [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) :
    ∃ original before result after,
      InternedFreshOrdinaryConstruction.build
        (.binder false (.var 0) : InternedNestedConstruction.Syntax Symbol Guard) [] InternedConstructorTemplates.empty = .done original before ∧
      RequireNode (SourceEqualityNeeded.build [[0]]) original before result after ∧
      MuStored valid after ∧ Annotated valid result := by
  let expression : InternedNestedConstruction.Syntax Symbol Guard := .binder false (.var 0)
  obtain ⟨original, before, built, stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed valid expression (by simp [expression, SourceEqualityAnnotationConstruction.Allowed])
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression original before built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result original before built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression original before built
  have costs : InternedFreshOrdinaryCostHeap.Heap before := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  obtain ⟨result, after, actual, _keeps, _available, _closed⟩ := SourceEqualityRequiredComplete.complete (SourceEqualityNeeded.build [[0]]) original before semantic.ready available closed
  have retained := SourceCurrentHereditaryRequiredMerge.node valid actual semantic costs available closed stored annotated
  exact ⟨original, before, result, after, built, actual, retained⟩

end MicroCFTA.HereditaryRequiredMergeRequiredKernels

#print axioms MicroCFTA.HereditaryRequiredMergeRequiredKernels.constructed_required_then_merge
#check @MicroCFTA.HereditaryRequiredMergeRequiredKernels.constructed_required_then_merge
#print axioms MicroCFTA.HereditaryRequiredMergeRequiredKernels.raw_self_selected
#check @MicroCFTA.HereditaryRequiredMergeRequiredKernels.raw_self_selected
