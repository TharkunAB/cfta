import MicroCFTA.SourceCurrentAllocatedNativeMuMeaning
open MicroCFTA Language BinderLanguage InternedBinderProtocol
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceCurrentAllocatedNativePairContexts SourceCurrentAllocatedNativeMuMeaning
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_least
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.body_monotone
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_unfold
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_sound
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_complete_of_descent
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.unfolded_language
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.mu_pair_descent
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_mu_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_mu_sound
#check @MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_least
#check @MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.body_monotone
#check @MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_unfold
#check @MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_sound
#check @MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_complete_of_descent
#check @MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.unfolded_language
#check @MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.mu_pair_descent
#check @MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_mu_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeMuMeaning.optionalBinder_mu_sound

namespace FreshMuChecks
noncomputable section
local instance : DecidableEq (EdgeKey Unit Unit) := Classical.typeDecidableEq _

-- 1. The repeated pair body is monotone in the fresh pair language.
example (holds : Unit → Term Unit → Bool) (output : InternedGuardedLanguage.Env Unit) :
    Monotone (fun candidate => InternedGuardedLanguage.meaning holds
      (InternedGuardedLanguage.bind output (.intersection 7 2) candidate)
      (SourceRecursiveIntersectionControl.repeatedValue (7, 2))) := body_monotone holds _ output (7, 2)

-- 2. The unused branch returns the exact existing value and heap.
example : SourceRecursiveIntersectionMaybeMu.maybeMu (7, 2) (.empty : Value Unit Unit) empty = .done .empty empty := by
  apply SourceRecursiveIntersectionMaybeMu.unused
  simp only [Value.free, List.not_mem_nil, not_false_eq_true]

-- 3. Actual fresh pair-self construction completes and has no accepted term.
theorem constructed_pair_self (holds : Unit → Term Unit → Bool) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu (7, 2)
      (SourceRecursiveIntersectionControl.repeatedValue (7, 2) : Value Unit Unit) empty = .done value after ∧
      ∀ output term, ¬ InternedGuardedLanguage.meaning holds output value term := by
  let body : Value Unit Unit := SourceRecursiveIntersectionControl.repeatedValue (7, 2)
  have available : Available (empty : State Unit Unit) body := by
    apply reference_available
    intro name member
    simp only [Value.free, List.mem_singleton, reduceCtorEq] at member
  obtain ⟨value, after, done, _, _, _, _⟩ := SourceRecursiveIntersectionMaybeMu.complete (7, 2) body empty
    empty_facts available InternedRecordCoherence.empty_correct.2 (.reference _)
  refine ⟨value, after, done, ?_⟩
  intro output term accepted
  rw [optionalBinder_least (7, 2) body empty SourceRecursiveIntersectionSemanticHeap.empty_heap
    InternedGuardedProbeHeap.empty_heap available value after done holds output] at accepted
  exact accepted (fun _ => False) (by
    intro subterm impossible
    simp only [body, SourceRecursiveIntersectionControl.repeatedValue, InternedGuardedLanguage.meaning,
      InternedGuardedLanguage.bind, ite_true] at impossible)

-- 4. The same unfold law applies when the actual constructor returns an unused body.
example (holds : Unit → Term Unit → Bool) (output : InternedGuardedLanguage.Env Unit) (term : Term Unit) :
    InternedGuardedLanguage.meaning holds output (.empty : Value Unit Unit) term ↔
      InternedGuardedLanguage.meaning holds
        (InternedGuardedLanguage.bind output (.intersection 7 2)
          (InternedGuardedLanguage.meaning holds output (.empty : Value Unit Unit))) .empty term := by
  apply optionalBinder_unfold (7, 2) .empty empty SourceRecursiveIntersectionSemanticHeap.empty_heap
    InternedGuardedProbeHeap.empty_heap (empty_available empty) .empty empty
  exact SourceRecursiveIntersectionMaybeMu.unused (7, 2) .empty empty (by simp [Value.free])

-- 5. Two Mu operands give strictly smaller original body ranks.
example (view : IntersectSchedule.View Unit) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (left : model.valid (.mu 7)) (right : model.valid (.mu 2)) (bound : Nat) (term : Term Unit)
    (accepted : RankedPair ranked.languages bound (IntersectSchedule.pair (.mu 7) (.mu 2)) term) :
    ∃ first second, first + second < bound ∧ IntersectSchedule.inputAt ranked.languages (view.body 7) first term ∧
      IntersectSchedule.inputAt ranked.languages (view.body 2) second term :=
  mu_pair_descent view model ranked (.mu 7) (.mu 2) left right (by intro same; cases same)
    (by intro same; cases same) (Or.inl ⟨7, rfl⟩) bound term accepted

-- 6. Left Mu unfolds without changing the ordinary right operand.
example (view : IntersectSchedule.View Unit) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (left : model.valid (.mu 7)) (right : model.valid (.node 2)) (bound : Nat) (term : Term Unit)
    (accepted : RankedPair ranked.languages bound (IntersectSchedule.pair (.mu 7) (.node 2)) term) :
    ∃ first second, first + second < bound ∧ IntersectSchedule.inputAt ranked.languages (view.body 7) first term ∧
      IntersectSchedule.inputAt ranked.languages (.node 2) second term :=
  mu_pair_descent view model ranked (.mu 7) (.node 2) left right (by intro same; cases same)
    (by intro same; cases same) (Or.inl ⟨7, rfl⟩) bound term accepted

-- 7. Right Mu unfolds without changing the ordinary left operand.
example (view : IntersectSchedule.View Unit) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (left : model.valid (.node 7)) (right : model.valid (.mu 2)) (bound : Nat) (term : Term Unit)
    (accepted : RankedPair ranked.languages bound (IntersectSchedule.pair (.node 7) (.mu 2)) term) :
    ∃ first second, first + second < bound ∧ IntersectSchedule.inputAt ranked.languages (.node 7) first term ∧
      IntersectSchedule.inputAt ranked.languages (view.body 2) second term :=
  mu_pair_descent view model ranked (.node 7) (.mu 2) left right (by intro same; cases same)
    (by intro same; cases same) (Or.inr ⟨2, rfl⟩) bound term accepted

-- 8. A common Mu term cannot have a combined original rank of zero.
example (view : IntersectSchedule.View Unit) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid)
    (left : model.valid (.mu 7)) (right : model.valid (.node 2)) (term : Term Unit) :
    ¬ RankedPair ranked.languages 0 (IntersectSchedule.pair (.mu 7) (.node 2)) term := by
  intro accepted
  obtain ⟨first, second, impossible, _, _⟩ := mu_pair_descent view model ranked (.mu 7) (.node 2)
    left right (by intro same; cases same) (by intro same; cases same) (Or.inl ⟨7, rfl⟩) 0 term accepted
  omega
end
end FreshMuChecks
