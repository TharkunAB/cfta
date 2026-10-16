import MicroCFTA.SourceCurrentAllocatedNativePairContexts

/-!
# Local language laws for actual optional intersection binders

The completed source constructor supplies its least-language equation.
Soundness tests that equation at the fixed original pair language.
Completeness uses strong induction on the sum of original input ranks.
That induction derives the new candidate-containment obligation.

The body soundness and completeness laws remain explicit component
assumptions. A checked execution proof must derive them from its body trace.
This module does not prove general checked request meaning or warm-cache
admissibility. It does not compare checked execution with an older worker.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMuMeaning
open Language BinderLanguage InternedBinderProtocol
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceCurrentAllocatedNativePairContexts

variable {Symbol Guard : Type}

/-- The actual completed optional binder denotes its original body transformer. -/
theorem optionalBinder_least [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (heap : InternedGuardedProbeHeap.Heap before) (available : Available before body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu key body before = .done value after)
    (holds : Guard → Term Symbol → Bool) (output : InternedGuardedLanguage.Env Symbol) :
    InternedGuardedLanguage.meaning holds output value = least (fun candidate =>
      InternedGuardedLanguage.meaning holds
        (InternedGuardedLanguage.bind output (.intersection key.1 key.2) candidate) body) :=
  (SourceRecursiveIntersectionGuardedEffects.optionalBinder_checked key body before semantic heap available).result
    value after done holds output

/-- The physical body transformer is monotone in its one new pair candidate. -/
theorem body_monotone (holds : Guard → Term Symbol → Bool) (body : Value Symbol Guard)
    (output : InternedGuardedLanguage.Env Symbol) (key : Nat × Nat) :
    Monotone (fun candidate => InternedGuardedLanguage.meaning holds
      (InternedGuardedLanguage.bind output (.intersection key.1 key.2) candidate) body) := by
  intro first second included
  apply InternedGuardedLanguage.meaning_mono holds body
  intro name term accepted
  by_cases same : name = .intersection key.1 key.2
  · simpa only [InternedGuardedLanguage.bind, same, ite_true] using included term
      (by simpa only [InternedGuardedLanguage.bind, same, ite_true] using accepted)
  · simpa only [InternedGuardedLanguage.bind, same, ite_false] using accepted

/-- The actual returned value satisfies the body equation at its own language. -/
theorem optionalBinder_unfold [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (heap : InternedGuardedProbeHeap.Heap before) (available : Available before body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu key body before = .done value after)
    (holds : Guard → Term Symbol → Bool) (output : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds output value term ↔
      InternedGuardedLanguage.meaning holds
        (InternedGuardedLanguage.bind output (.intersection key.1 key.2)
          (InternedGuardedLanguage.meaning holds output value)) body term := by
  have actual := optionalBinder_least key body before semantic heap available value after done holds output
  simp only [actual]
  exact least_fix _ (body_monotone holds body output key) term

/-- A sound body component gives one-sided soundness of the actual binder. -/
theorem optionalBinder_sound [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (heap : InternedGuardedProbeHeap.Heap before) (available : Available before body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu key body before = .done value after)
    (holds : Guard → Term Symbol → Bool) (languages : Nat → Lang Symbol)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : List Nat) (fresh : key ∉ domain.seen)
    (bodySound : ∀ inner, SoundPairs languages (SourceRecursiveIntersectionDomain.extend domain bindings key) inner →
      Included (InternedGuardedLanguage.meaning holds inner body) (PairLanguage languages key))
    (output : InternedGuardedLanguage.Env Symbol) (sound : SoundPairs languages domain output) :
    Included (InternedGuardedLanguage.meaning holds output value) (PairLanguage languages key) := by
  rw [optionalBinder_least key body before semantic heap available value after done holds output]
  exact least_le _ _ (bodySound _ (sound_extend languages domain output sound bindings key fresh))

/-- Strict original-rank descent discharges fresh candidate containment internally.
Only the body component and original rank descent are supplied. -/
theorem optionalBinder_complete_of_descent [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (heap : InternedGuardedProbeHeap.Heap before) (available : Available before body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu key body before = .done value after)
    (holds : Guard → Term Symbol → Bool) (ranks : Nat → Nat → Lang Symbol)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : List Nat) (fresh : key ∉ domain.seen)
    (leftBody rightBody : IntersectSchedule.Input)
    (descent : ∀ bound term, RankedPair ranks bound key term →
      ∃ first second, first + second < bound ∧
        IntersectSchedule.inputAt ranks leftBody first term ∧ IntersectSchedule.inputAt ranks rightBody second term)
    (bodyComplete : ∀ bound inner,
      CompletePairs ranks bound (SourceRecursiveIntersectionDomain.extend domain bindings key) inner →
      ∀ first second, first + second ≤ bound → ∀ term,
      IntersectSchedule.inputAt ranks leftBody first term → IntersectSchedule.inputAt ranks rightBody second term →
      InternedGuardedLanguage.meaning holds inner body term) :
    ∀ bound output, CompletePairs ranks bound domain output →
      Included (RankedPair ranks bound key) (InternedGuardedLanguage.meaning holds output value) := by
  intro bound
  induction bound using Nat.strongRecOn with
  | ind bound smaller =>
      intro output complete term accepted
      obtain ⟨first, second, less, leftAccepted, rightAccepted⟩ := descent bound term accepted
      let lower := first + second
      have oldComplete : CompletePairs ranks lower domain output :=
        complete_mono ranks lower bound (Nat.le_of_lt less) domain output complete
      have contains : Included (RankedPair ranks lower key) (InternedGuardedLanguage.meaning holds output value) :=
        smaller lower less output oldComplete
      have extended := complete_extend ranks lower domain output oldComplete bindings key fresh
        (InternedGuardedLanguage.meaning holds output value) contains
      exact (optionalBinder_unfold key body before semantic heap available value after done holds output term).mpr
        (bodyComplete lower _ extended first second (Nat.le_refl _) term leftAccepted rightAccepted)

/-- Unfold exactly those original operands whose source constructor is Mu. -/
def unfolded (view : IntersectSchedule.View Symbol) : IntersectSchedule.Input → IntersectSchedule.Input
  | .mu name => view.body name
  | input => input

/-- The fixed input model derives the language equation for each unfolded operand. -/
theorem unfolded_language (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (input : IntersectSchedule.Input) (valid : model.valid input) :
    IntersectSchedule.inputLanguage model.languages (unfolded view input) =
      IntersectSchedule.inputLanguage model.languages input := by
  cases input with
  | mu name => exact (model.body_exact name valid).symm
  | empty | node _ | union _ | ref _ => rfl

/-- Source Mu operands derive strict descent from the independent input rank laws. -/
theorem mu_pair_descent (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (left right : IntersectSchedule.Input)
    (leftValid : model.valid left) (rightValid : model.valid right)
    (leftNonempty : left ≠ .empty) (rightNonempty : right ≠ .empty)
    (recursive : (∃ name, left = .mu name) ∨ ∃ name, right = .mu name) (bound : Nat) (term : Term Symbol)
    (accepted : RankedPair ranked.languages bound (IntersectSchedule.pair left right) term) :
    ∃ first second, first + second < bound ∧
      IntersectSchedule.inputAt ranked.languages (unfolded view left) first term ∧
      IntersectSchedule.inputAt ranked.languages (unfolded view right) second term := by
  obtain ⟨first, second, bounded, leftAccepted, rightAccepted⟩ :=
    (IntersectSchedule.ranked_pair ranked.languages bound left right leftNonempty rightNonempty term).mp accepted
  by_cases leftMu : ∃ name, left = .mu name
  · obtain ⟨name, rfl⟩ := leftMu
    obtain ⟨one, smaller, leftBody⟩ := ranked.body name leftValid first term leftAccepted
    by_cases rightMu : ∃ name, right = .mu name
    · obtain ⟨other, rfl⟩ := rightMu
      obtain ⟨two, secondSmaller, rightBody⟩ := ranked.body other rightValid second term rightAccepted
      exact ⟨one, two, by omega, leftBody, rightBody⟩
    · have same : unfolded view right = right := by cases right <;> simp_all [unfolded]
      exact ⟨one, second, by omega, leftBody, same.symm ▸ rightAccepted⟩
  · obtain ⟨name, rfl⟩ := recursive.resolve_left leftMu
    obtain ⟨two, smaller, rightBody⟩ := ranked.body name rightValid second term rightAccepted
    have same : unfolded view left = left := by cases left <;> simp_all [unfolded]
    exact ⟨first, two, by omega, same.symm ▸ leftAccepted, rightBody⟩

/-- The actual binder is complete under a local body law for the three Mu branches.
The rank induction derives the extended context; no parent-result law is assumed. -/
theorem optionalBinder_mu_complete [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (left right : IntersectSchedule.Input)
    (leftValid : model.valid left) (rightValid : model.valid right)
    (leftNonempty : left ≠ .empty) (rightNonempty : right ≠ .empty)
    (recursive : (∃ name, left = .mu name) ∨ ∃ name, right = .mu name)
    (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (heap : InternedGuardedProbeHeap.Heap before) (available : Available before body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu (IntersectSchedule.pair left right) body before = .done value after)
    (holds : Guard → Term Symbol → Bool) (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : List Nat)
    (fresh : IntersectSchedule.pair left right ∉ domain.seen)
    (bodyComplete : ∀ bound inner,
      CompletePairs ranked.languages bound
        (SourceRecursiveIntersectionDomain.extend domain bindings (IntersectSchedule.pair left right)) inner →
      ∀ first second, first + second ≤ bound → ∀ term,
      IntersectSchedule.inputAt ranked.languages (unfolded view left) first term →
      IntersectSchedule.inputAt ranked.languages (unfolded view right) second term →
      InternedGuardedLanguage.meaning holds inner body term) :
    ∀ bound output, CompletePairs ranked.languages bound domain output → ∀ first second, first + second ≤ bound →
      ∀ term, IntersectSchedule.inputAt ranked.languages left first term →
      IntersectSchedule.inputAt ranked.languages right second term → InternedGuardedLanguage.meaning holds output value term := by
  have completed := optionalBinder_complete_of_descent (IntersectSchedule.pair left right) body before semantic heap available
    value after done holds ranked.languages domain bindings fresh (unfolded view left) (unfolded view right)
    (mu_pair_descent view model ranked left right leftValid rightValid leftNonempty rightNonempty recursive) bodyComplete
  intro bound output complete first second bounded term leftAccepted rightAccepted
  apply completed bound output complete term
  exact (IntersectSchedule.ranked_pair ranked.languages bound left right leftNonempty rightNonempty term).mpr
    ⟨first, second, bounded, leftAccepted, rightAccepted⟩

/-- The fixed input equations transfer a local unfolded-body soundness law. -/
theorem optionalBinder_mu_sound [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (left right : IntersectSchedule.Input) (leftValid : model.valid left) (rightValid : model.valid right)
    (leftNonempty : left ≠ .empty) (rightNonempty : right ≠ .empty)
    (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (heap : InternedGuardedProbeHeap.Heap before) (available : Available before body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu (IntersectSchedule.pair left right) body before = .done value after)
    (holds : Guard → Term Symbol → Bool) (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : List Nat)
    (fresh : IntersectSchedule.pair left right ∉ domain.seen)
    (bodySound : ∀ inner, SoundPairs model.languages
      (SourceRecursiveIntersectionDomain.extend domain bindings (IntersectSchedule.pair left right)) inner →
      Included (InternedGuardedLanguage.meaning holds inner body) (fun term =>
        IntersectSchedule.inputLanguage model.languages (unfolded view left) term ∧
        IntersectSchedule.inputLanguage model.languages (unfolded view right) term))
    (output : InternedGuardedLanguage.Env Symbol) (sound : SoundPairs model.languages domain output) :
    Included (InternedGuardedLanguage.meaning holds output value) (fun term =>
      IntersectSchedule.inputLanguage model.languages left term ∧ IntersectSchedule.inputLanguage model.languages right term) := by
  have built := optionalBinder_sound (IntersectSchedule.pair left right) body before semantic heap available value after done
    holds model.languages domain bindings fresh (fun inner contextValid term accepted => by
      have common := bodySound inner contextValid term accepted
      rw [unfolded_language view model left leftValid, unfolded_language view model right rightValid] at common
      exact (IntersectSchedule.pair_language model.languages left right leftNonempty rightNonempty term).mpr common)
    output sound
  intro term accepted
  exact (IntersectSchedule.pair_language model.languages left right leftNonempty rightNonempty term).mp (built term accepted)

end MicroCFTA.SourceCurrentAllocatedNativeMuMeaning
