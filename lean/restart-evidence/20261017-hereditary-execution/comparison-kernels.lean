import MicroCFTA.SourceCurrentHereditaryComparison
import MicroCFTA.SourceMergedComparisonCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.HereditaryComparisonIndependentChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityAnnotationLanguage SourceEqualityAnnotationConstruction
open SourceEqualityRequiredSemanticCache
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentHereditaryComparison (Effect)
open MergedSourceComparison (Result)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- The second completed comparison starts at the exact first returned cache. -/
theorem serial_comparisons [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (wide narrow : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideAvailable : Available before wide) (narrowAvailable : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (wideAnnotation : Annotated valid wide) (narrowAnnotation : Annotated valid narrow) (stored : MuStored valid before) :
    ∃ firstBound firstAnswer middle,
      MergedFreshOrdinaryComparison.check clear firstBound [] wide narrow before = .done firstAnswer middle ∧
      Effect valid before middle ∧
      ∃ secondBound secondAnswer after,
        MergedFreshOrdinaryComparison.check clear secondBound [] narrow wide middle = .done secondAnswer after ∧
        Effect valid middle after ∧ MuStored valid after := by
  obtain ⟨firstBound, firstAnswer, middle, firstDone, _⟩ := SourceMergedComparisonCompletion.check_complete clear before semantic
    [] wide narrow wideAvailable narrowAvailable wideClosed narrowClosed
  have first := SourceCurrentHereditaryComparison.check valid clear firstBound [] wide narrow before semantic costs
    wideAvailable narrowAvailable wideClosed narrowClosed wideAnnotation narrowAnnotation stored firstAnswer middle (firstDone _ (Nat.le_refl _))
  obtain ⟨secondBound, secondAnswer, after, secondDone, _⟩ := SourceMergedComparisonCompletion.check_complete clear middle first.semantic
    [] narrow wide (first.keeps.available _ narrowAvailable) (first.keeps.available _ wideAvailable) narrowClosed wideClosed
  have second := SourceCurrentHereditaryComparison.check valid clear secondBound [] narrow wide middle first.semantic first.costs
    (first.keeps.available _ narrowAvailable) (first.keeps.available _ wideAvailable) narrowClosed wideClosed narrowAnnotation wideAnnotation
    first.stored secondAnswer after (secondDone _ (Nat.le_refl _))
  exact ⟨firstBound, firstAnswer, middle, firstDone _ (Nat.le_refl _), first,
    secondBound, secondAnswer, after, secondDone _ (Nat.le_refl _), second, second.stored⟩

/-- An original recursive syntax family constructs its own finite annotated row read. -/
theorem recursive_source_read (smart : Bool) :
    let expression : InternedNestedConstruction.Syntax Nat Bool := .binder smart (.union
      [.node [.mk 0 true [.var 0]], .node [.mk 1 true []]])
    ∃ value before edges after, InternedFreshOrdinaryConstruction.build expression [] empty = .done value before ∧
      SourceEqualityProjectionRead.Read value before edges after ∧
      Effect (fun b => b = true) before after ∧
      (∀ edge ∈ edges, SourceCurrentHereditaryConstructors.Edge (fun b => b = true) edge) := by
  dsimp only
  let expression : InternedNestedConstruction.Syntax Nat Bool := .binder smart (.union
      [.node [.mk 0 true [.var 0]], .node [.mk 1 true []]])
  have allowed : Allowed (fun b : Bool => b = true) expression := by simp [expression, Allowed, ManyAllowed, EdgesAllowed]
  obtain ⟨value, before, built, stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed _ expression allowed
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value before built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result _ _ built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value before built
  have costs : CostHeap before := by simpa only [built, InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  obtain ⟨edges, after, actual, _⟩ := SourceEqualityProjectionRead.complete value before semantic available closed
  have checked := SourceCurrentHereditaryComparison.read _ actual semantic costs available closed annotated stored
  exact ⟨value, before, edges, after, built, actual, checked.1, checked.2.2.2⟩

/-- A constructed comparison return drives the literal ordered singleton zip. -/
theorem singleton_zip [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (wide narrow : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideAvailable : Available before wide) (narrowAvailable : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (wideAnnotation : Annotated valid wide) (narrowAnnotation : Annotated valid narrow) (stored : MuStored valid before) :
    ∃ fuel answer after,
      MergedSourceComparison.children (MergedFreshOrdinaryComparison.check clear fuel []) [wide] [narrow] before = .done answer after ∧
      Effect valid before after := by
  obtain ⟨fuel, answer, after, stable, _⟩ := SourceMergedComparisonCompletion.check_complete clear before semantic
    [] wide narrow wideAvailable narrowAvailable wideClosed narrowClosed
  have done := stable fuel (Nat.le_refl _)
  have zip : MergedSourceComparison.children (MergedFreshOrdinaryComparison.check clear fuel []) [wide] [narrow] before = .done answer after := by
    cases answer <;> simp only [MergedSourceComparison.children, done, Result.bind, Bool.false_eq_true, ↓reduceIte]
  have checked := SourceCurrentHereditaryComparison.children valid clear fuel [] [wide] [narrow] before semantic costs
    (fun value member => (List.mem_singleton.mp member) ▸ wideAvailable)
    (fun value member => (List.mem_singleton.mp member) ▸ narrowAvailable)
    (fun value member => (List.mem_singleton.mp member) ▸ wideClosed)
    (fun value member => (List.mem_singleton.mp member) ▸ narrowClosed)
    (fun value member => (List.mem_singleton.mp member) ▸ wideAnnotation)
    (fun value member => (List.mem_singleton.mp member) ▸ narrowAnnotation) stored answer after zip
  exact ⟨fuel, answer, after, zip, checked⟩

end MicroCFTA.HereditaryComparisonIndependentChecks

#print axioms MicroCFTA.HereditaryComparisonIndependentChecks.serial_comparisons
#check @MicroCFTA.HereditaryComparisonIndependentChecks.serial_comparisons
#print axioms MicroCFTA.HereditaryComparisonIndependentChecks.recursive_source_read
#check @MicroCFTA.HereditaryComparisonIndependentChecks.recursive_source_read
#print axioms MicroCFTA.HereditaryComparisonIndependentChecks.singleton_zip
#check @MicroCFTA.HereditaryComparisonIndependentChecks.singleton_zip
