import MicroCFTA.SourceEqualityEdits
import MicroCFTA.SourceEqualityRequiredForestMeaning

/-!
# Independent term conditions of simultaneous edit tries

Each leaf contributes its callback condition. Below a node, conditions apply
only to present child positions. Negative and missing indices impose no
condition. These semantics do not execute the physical edit worker.
-/
namespace MicroCFTA.SourceEqualityEditMeaning
open Language SourceEqualityEdits SourceEqualityNeededMap
open SourceEqualityNeededMeaning (childAt)

/-- Interpret each stored leaf condition at its existing term position. -/
def Matches (condition : Action → Term Symbol → Prop) : Edits Action → Term Symbol → Prop
  | .editAt action, term => condition action term
  | .editBelow entries, .node _ terms =>
      ∀ index edits, (index, edits) ∈ entries → ∀ term,
        childAt terms index = some term → Matches condition edits term
termination_by edits _ => sizeOf edits
decreasing_by
  have smaller := List.sizeOf_lt_of_mem ‹(index, edits) ∈ entries›
  simp only [Prod.mk.sizeOf_spec, Edits.editBelow.sizeOf_spec] at *
  omega

/-- Read callback conditions in original child order. -/
def Forest (condition : Action → Term Symbol → Prop) (entries : List (Int × Edits Action)) (offset : Nat) :
    List (Term Symbol) → Prop
  | [] => True
  | term :: terms =>
      (∀ edits, lookup (offset : Int) entries = some edits → Matches condition edits term) ∧
        Forest condition entries (offset + 1) terms

/-- The ordered forest condition checks exactly the selected existing positions. -/
theorem forest_exact (condition : Action → Term Symbol → Prop) (entries : List (Int × Edits Action))
    (offset : Nat) (terms : List (Term Symbol)) : Forest condition entries offset terms ↔
      ∀ query term, terms[query]? = some term → ∀ edits,
        lookup ((offset + query : Nat) : Int) entries = some edits → Matches condition edits term := by
  induction terms generalizing offset with
  | nil => simp [Forest]
  | cons term terms ih =>
      rw [Forest, ih]
      constructor
      · rintro ⟨first, rest⟩ query actual selected edits found
        cases query with
        | zero =>
            have same := Option.some.inj selected
            subst actual
            exact first edits (by simpa using found)
        | succ query => exact rest query actual selected edits (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found)
      · intro allTerms
        refine ⟨?_, ?_⟩
        · intro edits found
          exact allTerms 0 term rfl edits (by simpa using found)
        · intro query actual selected edits found
          exact allTerms (query + 1) actual selected edits (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found)

/-- Root child traversal has precisely the independent trie condition. -/
theorem forest_zero (condition : Action → Term Symbol → Prop) (entries : List (Int × Edits Action))
    (ordered : Ascending entries) (symbol : Symbol) (terms : List (Term Symbol)) :
    Forest condition entries 0 terms ↔ Matches condition (.editBelow entries) (.node symbol terms) := by
  rw [forest_exact, Matches]
  constructor
  · intro allTerms index edits member term selected
    have nonnegative : ¬ index < 0 := by
      intro negative
      simp [childAt, negative] at selected
    have natural : ((index.toNat : Nat) : Int) = index := by omega
    exact allTerms index.toNat term (by simpa only [childAt, ite_eq_right nonnegative] using selected)
      edits (by simpa only [Nat.zero_add, natural] using lookup_of_mem index entries edits ordered member)
  · intro allTerms query term selected edits found
    exact allTerms _ edits (lookup_mem _ entries edits found) term (by simpa [childAt] using selected)

/-- Semantic leaf narrowing conjoins the independent condition. -/
def narrow (condition : Action → Term Symbol → Prop) (edits : Edits Action) (language : Term Symbol → Prop) : Term Symbol → Prop :=
  fun term => language term ∧ Matches condition edits term

/-- The source signed right fold conjoins every edit condition at each present position. -/
theorem apply_exact (condition : Action → Term Symbol → Prop) (entries : List (Int × Edits Action))
    (languages : List (Term Symbol → Prop)) (terms : List (Term Symbol)) :
    All₂ (fun language term => language term) (SourceEqualityNeededAdjust.apply (narrow condition) entries languages) terms ↔
      All₂ (fun language term => language term) languages terms ∧
        ∀ index edits, (index, edits) ∈ entries → ∀ term, childAt terms index = some term → Matches condition edits term := by
  induction entries with
  | nil => simp [SourceEqualityNeededAdjust.apply]
  | cons entry rest ih =>
      obtain ⟨index, edits⟩ := entry
      change All₂ _ (SourceEqualityNeededAdjust.adjust index (narrow condition edits)
        (SourceEqualityNeededAdjust.apply (narrow condition) rest languages)) terms ↔ _
      rw [SourceEqualityNeededAdjustMeaning.adjust_exact (fun language term => language term)
        (Matches condition edits) (narrow condition edits) (fun _ _ => Iff.rfl), ih]
      constructor
      · rintro ⟨⟨before, prior⟩, selected⟩
        refine ⟨before, ?_⟩
        intro key child member
        rcases List.mem_cons.mp member with same | member
        · cases same; exact selected
        · exact prior key child member
      · rintro ⟨before, allChildren⟩
        exact ⟨⟨before, fun key child member => allChildren key child (List.mem_cons_of_mem _ member)⟩,
          allChildren index edits List.mem_cons_self⟩

/-- Physical child readback can use the source fold without comparing cross-cache output identities. -/
theorem fold_exact (condition : Action → Term Symbol → Prop) (lang : Node → Term Symbol → Prop)
    (entries : List (Int × Edits Action)) (ordered : Ascending entries) (values : List Node)
    (symbol : Symbol) (terms : List (Term Symbol)) :
    All₂ (fun language term => language term)
      (SourceEqualityNeededAdjust.apply (narrow condition) entries (values.map lang)) terms ↔
      All₂ lang values terms ∧ Matches condition (.editBelow entries) (.node symbol terms) := by
  rw [apply_exact, SourceEqualityRequiredForestMeaning.languages_exact]
  rw [← forest_zero condition entries ordered symbol terms, forest_exact]
  constructor
  · rintro ⟨before, allChildren⟩
    refine ⟨before, ?_⟩
    intro query term selected edits found
    exact allChildren _ edits (lookup_mem _ entries edits found) term (by simpa [childAt] using selected)
  · rintro ⟨before, allTerms⟩
    refine ⟨before, ?_⟩
    intro index edits member term selected
    have nonnegative : ¬ index < 0 := by
      intro negative
      simp [childAt, negative] at selected
    have natural : ((index.toNat : Nat) : Int) = index := by omega
    exact allTerms index.toNat term (by simpa only [childAt, ite_eq_right nonnegative] using selected)
      edits (by simpa only [Nat.zero_add, natural] using lookup_of_mem index entries edits ordered member)

end MicroCFTA.SourceEqualityEditMeaning
