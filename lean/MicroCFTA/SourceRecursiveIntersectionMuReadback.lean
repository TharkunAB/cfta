import MicroCFTA.SourceRecursiveIntersectionReplay
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence
import MicroCFTA.SourceRecursiveIntersectionGuardedEffects

/-!
# Actual Mu calls retain their domain, body result, and binder

The physical source extends its original domain before the body request.
Completed calls retain that exact domain and body result in every later
cache. The replayed optional binder has the independent least language of
that body at the original intersection reference. Input product language
and relation closure remain separate obligations.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionControl (identity pair)

/-- Actual completed Mu calls expose their exact domain and body representative in every later cache. -/
theorem mu_body_replay [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (leftAvailable : Available before.heap left) (rightAvailable : Available before.heap right)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : mu call domain left right before = .done value final) (growth : Extension final after) :
    ∃ first second extended bodyValue,
      identity left = some first ∧ identity right = some second ∧
      extended.key = SourceRecursiveIntersectionDomain.extend domain.key
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair first second) ∧
      Domain after extended ∧ Available after.heap bodyValue ∧
      SourceRecursiveIntersectionEnvironment.enter after.domains domain.key left right first second = (extended, after.domains) ∧
      call extended (body left) (body right) after = .done bodyValue after ∧
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair first second) bodyValue after.heap) after = .done value after := by
  cases first : identity left <;> cases second : identity right <;> simp only [mu, first, second] at done
  all_goals try cases done
  rename_i firstId secondId
  let actual := SourceRecursiveIntersectionEnvironment.enter before.domains domain.key left right firstId secondId
  let enteredState : Machine Symbol Guard := {before with domains := actual.2}
  obtain ⟨enteredValid, _, enteredDomain⟩ := entered before valid domain known left right leftAvailable rightAvailable firstId secondId
  have bodyLeft : Available enteredState.heap (body left) := body_available before.heap left leftAvailable
  have bodyRight : Available enteredState.heap (body right) := body_available before.heap right rightAvailable
  have checked := calls actual.1 (body left) (body right) enteredState enteredValid enteredDomain bodyLeft bodyRight
  change (call actual.1 (body left) (body right) enteredState).bind
    (fun bodyValue current => construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair firstId secondId) bodyValue current.heap) current) =
      .done value final at done
  cases returned : call actual.1 (body left) (body right) enteredState with
  | failed failure state => simp only [returned, Result.bind] at done; cases done
  | done bodyValue middle =>
      have middleValid : Valid middle := by simpa only [returned, Result.state] using checked.valid
      have bodyAvailable := checked.result bodyValue middle returned
      have bodyGrowth : Extension enteredState middle := by simpa only [returned, Result.state] using checked.extension
      have built : construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair firstId secondId) bodyValue middle.heap) middle =
          .done value final := by simpa only [returned, Result.bind] using done
      have binderChecked := construction_checked middle middleValid
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair firstId secondId) bodyValue middle.heap) Available
        (SourceRecursiveIntersectionMaybeMu.verified (pair firstId secondId) bodyValue middle.heap middleValid.1 bodyAvailable)
      have binderGrowth : Extension middle final := by simpa only [built, Result.state] using binderChecked.extension
      have later := binderGrowth.trans growth
      have total := bodyGrowth.trans later
      let key := SourceRecursiveIntersectionDomain.extend domain.key
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair firstId secondId)
      have allocation : SourceRecursiveIntersectionEnvironment.enter after.domains domain.key left right firstId secondId =
          (actual.1, after.domains) := make_domain_replay before.domains after.domains key valid.2 total.domains
      exact ⟨firstId, secondId, actual.1, bodyValue, rfl, rfl,
        SourceRecursiveIntersectionSchedule.entered_key before.domains valid.2 domain.key left right firstId secondId,
        enteredDomain.grows actual.1 total, later.available bodyValue bodyAvailable, allocation,
        replay actual.1 (body left) (body right) enteredState after bodyValue middle enteredValid enteredDomain bodyLeft bodyRight returned later,
        maybeMu_replay (pair firstId secondId) bodyValue middle after middleValid bodyAvailable value final built growth⟩

/-- Actual Mu completion has the independent least language of its exact replayed body at its original repeated-pair reference. -/
theorem mu_language [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (leftAvailable : Available before.heap left) (rightAvailable : Available before.heap right)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after.heap)
    (guarded : InternedGuardedProbeHeap.Heap after.heap)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : mu call domain left right before = .done value final) (growth : Extension final after) :
    ∃ first second extended bodyValue,
      identity left = some first ∧ identity right = some second ∧
      extended.key = SourceRecursiveIntersectionDomain.extend domain.key
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair first second) ∧
      Domain after extended ∧ Available after.heap bodyValue ∧
      SourceRecursiveIntersectionEnvironment.enter after.domains domain.key left right first second = (extended, after.domains) ∧
      call extended (body left) (body right) after = .done bodyValue after ∧
      ∀ holds ambient, InternedGuardedLanguage.meaning holds ambient value = BinderLanguage.least (fun candidate =>
        InternedGuardedLanguage.meaning holds (InternedGuardedLanguage.bind ambient
          (.intersection (pair first second).1 (pair first second).2) candidate) bodyValue) := by
  obtain ⟨first, second, extended, bodyValue, leftId, rightId, key, known, available, entered, returned, built⟩ :=
    mu_body_replay call calls replay domain left right before after valid known leftAvailable rightAvailable value final done growth
  obtain ⟨heap, completed, _⟩ := construction_done _ after value after built
  have language := (SourceRecursiveIntersectionGuardedEffects.optionalBinder_checked (pair first second) bodyValue after.heap
    semantic guarded available).result value heap completed
  exact ⟨first, second, extended, bodyValue, leftId, rightId, key, known, available, entered, returned, language⟩

/-- Actual Mu language is the least language of its successful extended-domain body calls. -/
theorem mu_language_calls [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (leftAvailable : Available before.heap left) (rightAvailable : Available before.heap right)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after.heap)
    (guarded : InternedGuardedProbeHeap.Heap after.heap)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : mu call domain left right before = .done value final) (growth : Extension final after) :
    ∃ first second extended,
      identity left = some first ∧ identity right = some second ∧
      extended.key = SourceRecursiveIntersectionDomain.extend domain.key
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair first second) ∧
      Domain after extended ∧
      SourceRecursiveIntersectionEnvironment.enter after.domains domain.key left right first second = (extended, after.domains) ∧
      ∀ holds ambient, InternedGuardedLanguage.meaning holds ambient value = BinderLanguage.least (fun candidate term =>
        ∃ result, call extended (body left) (body right) after = .done result after ∧
          InternedGuardedLanguage.meaning holds (InternedGuardedLanguage.bind ambient
            (.intersection (pair first second).1 (pair first second).2) candidate) result term) := by
  obtain ⟨first, second, extended, bodyValue, leftId, rightId, key, known, _, entered, returned, language⟩ :=
    mu_language call calls replay domain left right before after valid known leftAvailable rightAvailable semantic guarded value final done growth
  refine ⟨first, second, extended, leftId, rightId, key, known, entered, ?_⟩
  intro holds ambient
  apply (language holds ambient).trans
  apply BinderLanguage.least_congr
  intro candidate term
  constructor
  · intro accepted
    exact ⟨bodyValue, returned, accepted⟩
  · rintro ⟨result, done, accepted⟩
    have same := (Result.done.inj (done.symm.trans returned)).1
    rw [same] at accepted
    exact accepted

/-- The actual Mu result and its replayed body satisfy the complete unfolding equation at the original pair. -/
theorem mu_unfold_language [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (before after : Machine Symbol Guard) (valid : Valid before) (known : Domain before domain)
    (leftAvailable : Available before.heap left) (rightAvailable : Available before.heap right)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after.heap)
    (guarded : InternedGuardedProbeHeap.Heap after.heap)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : mu call domain left right before = .done value final) (growth : Extension final after) :
    ∃ first second extended bodyValue,
      identity left = some first ∧ identity right = some second ∧ Domain after extended ∧
      call extended (body left) (body right) after = .done bodyValue after ∧
      ∀ holds ambient term, InternedGuardedLanguage.meaning holds ambient value term ↔
        InternedGuardedLanguage.meaning holds (InternedGuardedLanguage.bind ambient
          (.intersection (pair first second).1 (pair first second).2)
          (InternedGuardedLanguage.meaning holds ambient value)) bodyValue term := by
  obtain ⟨first, second, extended, bodyValue, leftId, rightId, _, known, _, _, returned, language⟩ :=
    mu_language call calls replay domain left right before after valid known leftAvailable rightAvailable semantic guarded value final done growth
  refine ⟨first, second, extended, bodyValue, leftId, rightId, known, returned, ?_⟩
  intro holds ambient term
  have positive : BinderLanguage.Monotone (fun candidate => InternedGuardedLanguage.meaning holds
      (InternedGuardedLanguage.bind ambient (.intersection (pair first second).1 (pair first second).2) candidate) bodyValue) := by
    intro smaller larger included
    apply InternedGuardedLanguage.meaning_mono
    intro name tree accepted
    by_cases same : name = .intersection (pair first second).1 (pair first second).2
    · simp only [InternedGuardedLanguage.bind, same, ↓reduceIte] at accepted ⊢
      exact included tree accepted
    · simpa only [InternedGuardedLanguage.bind, same, ↓reduceIte] using accepted
  rw [language holds ambient]
  exact BinderLanguage.least_fix _ positive term

end MicroCFTA.SourceRecursiveIntersectionKernel
