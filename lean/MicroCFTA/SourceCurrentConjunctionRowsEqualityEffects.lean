import MicroCFTA.SourceCurrentConjunctionRowsWorker
import MicroCFTA.SourceCurrentConjunctionRowsAllocation

set_option autoImplicit false
open scoped Classical

/-! Equality-cache effects at actual tuple endpoints. -/
namespace MicroCFTA.SourceCurrentConjunctionRowsEqualityEffects
open InternedConstructorTemplates
open InternedNestedProvenance (Edges)
open SourceCurrentConjunctionRowsWorker
variable {Symbol Formula A B : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid
local notation "Grows" => SourceEqualityConstraintMemoAllocation.Grows
local notation "Fields" => SourceCurrentConjunctionEquality.Fields

private theorem map_state (actual : Outcome Symbol Formula A) (f : A → B) :
    (actual.bind (fun value after => .done (f value) after)).state = actual.state := by
  cases actual <;> rfl
private theorem bind_equality (actual : Outcome Symbol Formula A)
    (next : A → Physical → Outcome Symbol Formula B)
    (same : ∀ value after, (next value after).state.equality = after.equality) :
    (actual.bind next).state.equality = actual.state.equality := by
  cases actual with
  | done value after => exact same value after
  | failed fault after => rfl

private theorem projections_equality (p h : Nat) (jobs : List (Job Symbol Formula)) (before : Physical) :
    (projections p h jobs before).state.equality = before.equality := by
  induction jobs generalizing before with
  | nil => rfl
  | cons job jobs ih =>
    rcases job with ⟨forest, path⟩
    cases actual : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap with
    | done value heap =>
      simp only [projections, actual, map_state]
      exact ih ⟨heap, before.equality⟩
    | pending key heap | unresolved key heap | exhausted key heap =>
      simp only [projections, actual, Outcome.state]

private theorem classes_equality (p h : Nat) (forests : List (List (Value Symbol Guard)))
    (constraints : EqualityNormalize.Constraints) (before : Physical) :
    (classes p h forests constraints before).state.equality = before.equality := by
  induction constraints generalizing before with
  | nil => rfl
  | cons paths constraints ih =>
    simp only [classes]
    exact (bind_equality _ _ (by
      intro projected middle
      rw [map_state]
      exact ih middle)).trans
        (projections_equality p h (SourceCurrentConjunctionCompletionReads.jobs forests paths) before)

private theorem requirements_equality (p h : Nat) (edges : List (EdgeValue Symbol Guard))
    (constraints : EqualityNormalize.Constraints) (before : Physical) :
    (requirements p h edges constraints before).state.equality = before.equality := by
  unfold requirements
  rw [map_state]
  exact classes_equality p h (edges.map EdgeValue.children) constraints before

private theorem tuple_equality (p h : Nat) (edges : List (EdgeValue Symbol Guard)) (before : Physical) :
    (tuple p h edges before).state.equality = (SourceCurrentConjunctionEquality.fold edges before.equality).2 := by
  unfold tuple
  generalize folded : SourceCurrentConjunctionEquality.fold edges before.equality = actual
  rcases actual with ⟨answer, saved⟩
  dsimp only
  cases answer with
  | error message => rfl
  | ok value => cases value with
    | none => rfl
    | some result =>
      cases selected : SourceEqualityInheritedPayload.classes result.payload with
      | none => simp only [selected, Outcome.state]
      | some constraints =>
        simp only [selected, map_state]
        exact requirements_equality p h edges constraints (⟨before.heap, saved⟩ : Physical)

private theorem tuple_cache (p h : Nat) (edges : List (EdgeValue Symbol Guard)) (before : Physical)
    (valid : Valid before.equality)
    (fields : ∀ edge ∈ edges, SourceCurrentConjunctionEquality.FieldAvailable before.equality edge.entry.key.constraint) :
    Valid (tuple p h edges before).state.equality ∧ Grows before.equality (tuple p h edges before).state.equality := by
  obtain ⟨_, _, ready, _, _, _, growth⟩ :=
    SourceCurrentConjunctionEquality.fold_correct edges before.equality valid fields
  rw [tuple_equality]
  exact ⟨ready, growth⟩

private theorem tuples_cache (p h : Nat) (tuples : List (List (EdgeValue Symbol Guard))) (before : Physical)
    (valid : Valid before.equality)
    (fields : ∀ edges ∈ tuples, ∀ edge ∈ edges,
      SourceCurrentConjunctionEquality.FieldAvailable before.equality edge.entry.key.constraint) :
    Valid (SourceCurrentConjunctionRowsWorker.tuples p h tuples before).state.equality ∧
      Grows before.equality (SourceCurrentConjunctionRowsWorker.tuples p h tuples before).state.equality := by
  induction tuples generalizing before with
  | nil => exact ⟨valid, SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  | cons edges remaining ih =>
    have first := tuple_cache p h edges before valid (fields edges List.mem_cons_self)
    cases actual : tuple p h edges before with
    | failed fault middle =>
      simp only [actual, Outcome.state] at first
      simp only [SourceCurrentConjunctionRowsWorker.tuples, actual, Outcome.bind, Outcome.state]
      exact first
    | done row middle =>
      simp only [actual, Outcome.state] at first
      have later := ih middle first.1 (fun edges member edge present =>
        (fields edges (List.mem_cons_of_mem _ member) edge present).grows first.2)
      have checked := And.intro later.1
        (SourceCurrentConjunctionEquality.grows_trans first.2 later.2)
      simp only [SourceCurrentConjunctionRowsWorker.tuples, actual, Outcome.bind]
      cases suffix : SourceCurrentConjunctionRowsWorker.tuples p h remaining middle <;>
        simpa only [suffix, Outcome.state] using checked

/-- Every actual tuple outcome retains equality validity and fields on the initial heap. -/
theorem tuple_cache_effects (p h : Nat) (edges : List (EdgeValue Symbol Guard)) (before : Physical)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (resident : Edges before.heap edges) :
    let actual := tuple p h edges before
    Valid actual.state.equality ∧ Grows before.equality actual.state.equality ∧
      Fields actual.state.equality before.heap := by
  have checked := tuple_cache p h edges before ready.valid
    (fun edge member => ready.fields edge.entry.key edge (resident edge member))
  exact ⟨checked.1, checked.2, ready.fields.grows checked.2⟩

/-- Actual tuple-list failures and completions retain equality state and initial-heap fields. -/
theorem tuples_cache_effects (p h : Nat) (tuples : List (List (EdgeValue Symbol Guard))) (before : Physical)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (resident : ∀ edges ∈ tuples, Edges before.heap edges) :
    let actual := SourceCurrentConjunctionRowsWorker.tuples p h tuples before
    Valid actual.state.equality ∧ Grows before.equality actual.state.equality ∧
      Fields actual.state.equality before.heap := by
  have checked := tuples_cache p h tuples before ready.valid
    (fun edges member edge present => ready.fields edge.entry.key edge (resident edges member edge present))
  exact ⟨checked.1, checked.2, ready.fields.grows checked.2⟩

end MicroCFTA.SourceCurrentConjunctionRowsEqualityEffects
