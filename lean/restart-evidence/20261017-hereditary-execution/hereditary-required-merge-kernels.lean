import MicroCFTA.SourceCurrentHereditaryMergeStore
import MicroCFTA.SourceCurrentHereditaryExposure
import MicroCFTA.SourceCurrentMemoMergeCompletion
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.SourceEqualityAnnotationHeap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.HereditaryMergeStoreKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryConstruction
open SourceEqualityRequiredSemanticCache SourceCurrentMemoMergeGraph
variable {Symbol Guard : Type}

/-- An allowed source crosses an unrelated cap, actual Merge, warm replay, and actual head read. -/
theorem constructed_cap_merge_warm_head [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (capSymbol : Symbol) (capGuard : Guard) (invalid : ¬ valid capGuard)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed valid expression) :
    ∃ original builtHeap result after memo head final,
      InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done original builtHeap ∧
      let capHeap := (run (makeEdge capSymbol capGuard []) builtHeap).2
      ¬ SourceEqualityAnnotationHeap.Heap valid capHeap ∧
      Call clear top original capHeap empty result after memo ∧
      Call clear top original after memo result after memo ∧
      SourceEqualityRequiredHead.Head result after head final ∧
      MuStored valid after ∧ MuStored valid final ∧ Annotated valid result ∧ Annotated valid head := by
  obtain ⟨original, builtHeap, built, stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed valid expression allowed
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression original builtHeap built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result original builtHeap built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression original builtHeap built
  have costs : InternedFreshOrdinaryCostHeap.Heap builtHeap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  have nilInputs : InternedNestedProvenance.Values builtHeap [] := by intro value impossible; cases impossible
  have cap := SourceEqualityRequiredCache.edge capSymbol capGuard [] builtHeap semantic.ready nilInputs
  have capSemantic := SourceEqualityRequiredSemanticCache.edge capSymbol capGuard [] builtHeap semantic nilInputs
  have capCosts : InternedFreshOrdinaryCostHeap.Heap (run (makeEdge capSymbol capGuard []) builtHeap).2 := costs
  have capStored := stored.makeEdge capSymbol capGuard []
  have capAvailable := cap.1.available original available
  have notHeap : ¬ SourceEqualityAnnotationHeap.Heap valid (run (makeEdge capSymbol capGuard []) builtHeap).2 := by
    intro allGuards
    have bounded := allGuards _ _ cap.2.1
    have key := InternedOrdinaryAbsenceReplay.makeEdge_key capSymbol capGuard [] builtHeap semantic.ready.semantic.1.normal.facts.coherent
    rw [key] at bounded
    exact invalid bounded
  obtain ⟨result, after, memo, actual, _physical⟩ := SourceCurrentMemoMergeCompletion.call_complete clear top original
    (run (makeEdge capSymbol capGuard []) builtHeap).2 empty capSemantic capCosts
    (SourceCurrentMemoMergeEffects.stored_empty _) capAvailable
  obtain ⟨effect, physical, annotations, retained, returned⟩ := SourceCurrentHereditaryMergeStore.call valid topValid actual
    capSemantic capCosts (SourceCurrentMemoMergeEffects.stored_empty _) (SourceCurrentHereditaryMerge.stored_empty valid)
    capStored capAvailable annotated
  have resultAnnotated := returned.2 annotated
  obtain ⟨entry, found, same⟩ := actual.present
  have warm : Call clear top original after memo result after memo := by rw [same]; exact .hit found
  have warmReturned := SourceCurrentHereditaryMergeStore.call valid topValid warm effect.semantic effect.costs physical annotations retained
    (effect.keeps.available original capAvailable) annotated
  obtain ⟨head, final, headActual, _headPhysical⟩ := SourceEqualityRequiredHead.complete result after effect.keeps.ready returned.1.1 (returned.1.2 closed)
  have headReturned := SourceCurrentHereditaryExposure.head valid headActual effect.keeps.ready returned.1.1 (returned.1.2 closed)
    resultAnnotated warmReturned.2.2.2.1
  exact ⟨original, builtHeap, result, after, memo, head, final, built, notHeap, actual, warm, headActual,
    retained, headReturned.1, resultAnnotated, headReturned.2⟩

/-- Every produced warm call retains the same causal store and the complete previous physical state. -/
theorem produced_warm_store [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (input result : Value Symbol Guard) (before after : State Symbol Guard) (saved : Memo Symbol Guard)
    (actual : Call clear top input before empty result after saved)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before input) (annotated : Annotated valid input) (stored : MuStored valid before) :
    ∃ _warm : Call clear top input after saved result after saved,
      MuStored valid after ∧ Annotated valid result ∧
      (∀ later other completed, Call clear top input after saved later other completed →
        other = after ∧ completed = saved ∧ later = result) := by
  obtain ⟨effect, physical, annotations, retained, output⟩ := SourceCurrentHereditaryMergeStore.cold valid topValid actual semantic costs stored available annotated
  obtain ⟨entry, found, rfl⟩ := actual.present
  have warm : Call clear top input after saved entry.result after saved := .hit found
  have checked := SourceCurrentHereditaryMergeStore.call valid topValid warm effect.semantic effect.costs physical annotations retained
    (effect.keeps.available input available) annotated
  exact ⟨warm, checked.2.2.2.1, output, fun _ _ _ next => next.hit_unchanged entry found⟩

end MicroCFTA.HereditaryMergeStoreKernels

#print axioms MicroCFTA.HereditaryMergeStoreKernels.constructed_cap_merge_warm_head
#check @MicroCFTA.HereditaryMergeStoreKernels.constructed_cap_merge_warm_head
#print axioms MicroCFTA.HereditaryMergeStoreKernels.produced_warm_store
#check @MicroCFTA.HereditaryMergeStoreKernels.produced_warm_store
