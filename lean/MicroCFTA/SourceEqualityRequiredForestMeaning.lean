import MicroCFTA.SourceEqualityNeededAdjustMeaning

/-!
# Ordered term requirements and the signed source fold

The child graph reads one requirement at each original position. Its term
predicate agrees with the source adjustment fold on languages. This comparison
does not require physical outputs from different caches to be equal.
-/
namespace MicroCFTA.SourceEqualityRequiredForestMeaning
open Language SourceEqualityNeeded SourceEqualityNeededMeaning SourceEqualityNeededMap

/-- Check each present term at its original child position. -/
def Required (entries : List (Int × Needed)) (offset : Nat) : List (Term Symbol) → Prop
  | [] => True
  | term :: terms =>
      (∀ needed, lookup (offset : Int) entries = some needed → Matches needed term) ∧
      Required entries (offset + 1) terms

/-- Ordered traversal checks precisely the selected existing positions. -/
theorem required_exact (entries : List (Int × Needed)) (offset : Nat) (terms : List (Term Symbol)) :
    Required entries offset terms ↔
      ∀ query term, terms[query]? = some term →
        ∀ needed, lookup ((offset + query : Nat) : Int) entries = some needed → Matches needed term := by
  induction terms generalizing offset with
  | nil => simp [Required]
  | cons term terms ih =>
      rw [Required, ih]
      constructor
      · rintro ⟨first, rest⟩ query actual selected needed found
        cases query with
        | zero =>
            have same : term = actual := Option.some.inj selected
            subst actual
            exact first needed (by simpa using found)
        | succ query =>
            exact rest query actual selected needed (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found)
      · intro allTerms
        refine ⟨?_, ?_⟩
        · intro needed found
          exact allTerms 0 term rfl needed (by simpa using found)
        · intro query actual selected needed found
          exact allTerms (query + 1) actual selected needed (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found)

/-- At the root, signed map membership gives the same conditional requirements. -/
theorem required_zero (entries : List (Int × Needed)) (ordered : Ascending entries)
    (terms : List (Term Symbol)) :
    Required entries 0 terms ↔ ∀ index needed, (index, needed) ∈ entries →
      ∀ term, childAt terms index = some term → Matches needed term := by
  rw [required_exact]
  constructor
  · intro allTerms index needed member term selected
    have nonnegative : ¬ index < 0 := by
      intro negative
      simp [childAt, negative] at selected
    have natural : ((index.toNat : Nat) : Int) = index := by omega
    exact allTerms index.toNat term (by simpa only [childAt, ite_eq_right nonnegative] using selected)
      needed (by simpa only [Nat.zero_add, natural] using lookup_of_mem index entries needed ordered member)
  · intro allTerms query term selected needed found
    have member := lookup_mem _ entries needed found
    exact allTerms _ needed member term (by simpa [childAt] using selected)

/-- Mapping values to their languages preserves the ordered forest relation. -/
theorem languages_exact (lang : Node → Term Symbol → Prop) (values : List Node) (terms : List (Term Symbol)) :
    All₂ (fun language term => language term) (values.map lang) terms ↔ All₂ lang values terms := by
  induction values generalizing terms with
  | nil => cases terms <;> constructor <;> intro accepted <;> cases accepted <;> exact .nil
  | cons value values ih =>
      cases terms with
      | nil => constructor <;> intro accepted <;> cases accepted
      | cons term terms =>
          constructor
          · intro accepted
            cases accepted with
            | cons first rest => exact .cons first ((ih terms).mp rest)
          · intro accepted
            cases accepted with
            | cons first rest => exact .cons first ((ih terms).mpr rest)

/-- Semantic intersection is the exact per-node contract used by the source fold. -/
def narrow (needed : Needed) (language : Term Symbol → Prop) : Term Symbol → Prop :=
  fun term => language term ∧ Matches needed term

/-- The signed right fold and the original-position scan have the same forest meaning. -/
theorem fold_exact (lang : Node → Term Symbol → Prop) (entries : List (Int × Needed))
    (ordered : Ascending entries) (values : List Node) (terms : List (Term Symbol)) :
    All₂ (fun language term => language term)
      (SourceEqualityNeededAdjust.apply narrow entries (values.map lang)) terms ↔
      All₂ lang values terms ∧ Required entries 0 terms := by
  rw [SourceEqualityNeededAdjustMeaning.apply_exact (fun language term => language term) narrow
    (fun _ _ _ => Iff.rfl), languages_exact, required_zero entries ordered]

/-- The actual arity check converts the scan to the complete required-trie meaning. -/
theorem checked_exact (lang : Node → Term Symbol → Prop) (entries : List (Int × Needed))
    (valid : Valid (.node entries))
    (nonnegative : ∀ index needed, (index, needed) ∈ entries → 0 ≤ index)
    (values : List Node) (symbol : Symbol) (terms : List (Term Symbol))
    (rowFits : fits (.node entries) values.length = true) :
    (All₂ lang values terms ∧ Required entries 0 terms) ↔
      All₂ lang values terms ∧ Matches (.node entries) (.node symbol terms) := by
  have ordered := (show Ascending entries ∧ _ from (by simpa only [Valid] using valid)).1
  have checked := SourceEqualityNeededAdjustMeaning.checked_row_exact
    (fun language term => language term) narrow (fun _ _ _ => Iff.rfl)
    entries valid nonnegative (values.map lang) symbol terms (by simpa using rowFits)
  rw [languages_exact] at checked
  exact (fold_exact lang entries ordered values terms).symm.trans checked

end MicroCFTA.SourceEqualityRequiredForestMeaning
