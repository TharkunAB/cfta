import MicroCFTA.SourceSynthesisSelections

/-!
# Argument properties through the literal selection table

The proofs follow the source subsequence and permutation workers.
The interleave worker retains properties through its prefix function.
The last-winner lookup needs no distinct-name premise.
-/
set_option maxHeartbeats 2000000

namespace MicroCFTA.SourceSynthesisSelectionOrigins
open SourceSynthesisSelections

variable {α β : Type}

private theorem subsequence_fold_preserves (P : α → Prop) (value : α)
    (entries : List (List α)) (valueP : P value)
    (entriesP : ∀ selected ∈ entries, ∀ x ∈ selected, P x) :
    ∀ selected ∈ entries.foldr (fun chosen later => chosen :: (value :: chosen) :: later) [],
      ∀ x ∈ selected, P x := by
  cases entries with
  | nil => intro selected member; cases member
  | cons first rest =>
      intro selected member
      rcases List.mem_cons.mp member with same | later
      · subst selected
        exact entriesP first List.mem_cons_self
      · rcases List.mem_cons.mp later with same | remaining
        · subst selected
          intro x present
          rcases List.mem_cons.mp present with same | inside
          · subst x; exact valueP
          · exact entriesP first List.mem_cons_self x inside
        · exact subsequence_fold_preserves P value rest valueP
            (fun chosen present => entriesP chosen (List.mem_cons.mpr (.inr present)))
            selected remaining
termination_by entries.length

/-- Every source nonempty subsequence retains the input element property. -/
theorem nonEmptySubsequences_preserves (P : α → Prop) (values : List α)
    (inputs : ∀ x ∈ values, P x) :
    ∀ selected ∈ nonEmptySubsequences values, ∀ x ∈ selected, P x := by
  cases values with
  | nil => intro selected member; cases member
  | cons first rest =>
      have firstP : P first := inputs first List.mem_cons_self
      have restP : ∀ x ∈ rest, P x := fun x member => inputs x (List.mem_cons.mpr (.inr member))
      intro selected member
      rcases List.mem_cons.mp member with same | later
      · subst selected
        intro x present
        have same := List.mem_singleton.mp present
        subst x
        exact firstP
      · exact subsequence_fold_preserves P first _ firstP
          (nonEmptySubsequences_preserves P rest restP) selected later
termination_by values.length

/-- The empty and nonempty source subsequences retain the same property. -/
theorem subsequences_preserves (P : α → Prop) (values : List α)
    (inputs : ∀ x ∈ values, P x) :
    ∀ selected ∈ subsequences values, ∀ x ∈ selected, P x := by
  intro selected member
  rcases List.mem_cons.mp member with same | later
  · subst selected
    intro x present
    cases present
  · exact nonEmptySubsequences_preserves P values inputs selected later

/-- Both outputs of the literal interleave worker retain their element properties. -/
theorem interleaveAux_preserves (P : α → Prop) (Q : β → Prop)
    (value : α) (suffix selected : List α) (initial : List α → β) (later : List β)
    (valueP : P value) (suffixP : ∀ x ∈ suffix, P x) (selectedP : ∀ x ∈ selected, P x)
    (initialP : ∀ values, (∀ x ∈ values, P x) → Q (initial values))
    (laterP : ∀ x ∈ later, Q x) :
    (∀ x ∈ (interleaveAux value suffix initial selected later).1, P x) ∧
    (∀ x ∈ (interleaveAux value suffix initial selected later).2, Q x) := by
  cases selected with
  | nil => exact ⟨suffixP, laterP⟩
  | cons first rest =>
      have firstP : P first := selectedP first List.mem_cons_self
      have restP : ∀ x ∈ rest, P x := fun x member => selectedP x (List.mem_cons.mpr (.inr member))
      have initialTail : ∀ values, (∀ x ∈ values, P x) → Q (initial (first :: values)) := by
        intro values inputs
        apply initialP
        intro x member
        rcases List.mem_cons.mp member with same | inside
        · subst x; exact firstP
        · exact inputs x inside
      obtain ⟨leftP, rightP⟩ := interleaveAux_preserves P Q value suffix rest
        (fun values => initial (first :: values)) later valueP suffixP restP initialTail laterP
      constructor
      · intro x member
        rcases List.mem_cons.mp member with same | inside
        · subst x; exact firstP
        · exact leftP x inside
      · intro x member
        rcases List.mem_cons.mp member with same | inside
        · subst x
          apply initialP
          intro y present
          rcases List.mem_cons.mp present with same | tail
          · subst y; exact valueP
          · rcases List.mem_cons.mp tail with same | remaining
            · subst y; exact firstP
            · exact leftP y remaining
        · exact rightP x inside
termination_by selected.length

/-- Every interleaved permutation and every later row retains the input property. -/
theorem interleave_preserves (P : α → Prop) (value : α) (suffix selected : List α)
    (later : List (List α)) (valueP : P value) (suffixP : ∀ x ∈ suffix, P x)
    (selectedP : ∀ x ∈ selected, P x) (laterP : ∀ chosen ∈ later, ∀ x ∈ chosen, P x) :
    ∀ chosen ∈ interleave value suffix selected later, ∀ x ∈ chosen, P x :=
  (interleaveAux_preserves P (fun values => ∀ x ∈ values, P x) value suffix selected id later
    valueP suffixP selectedP (fun _ inputs => inputs) laterP).2

private theorem interleave_fold_preserves (P : α → Prop) (value : α) (suffix : List α)
    (entries later : List (List α)) (valueP : P value) (suffixP : ∀ x ∈ suffix, P x)
    (entriesP : ∀ chosen ∈ entries, ∀ x ∈ chosen, P x)
    (laterP : ∀ chosen ∈ later, ∀ x ∈ chosen, P x) :
    ∀ chosen ∈ entries.foldr (interleave value suffix) later, ∀ x ∈ chosen, P x := by
  cases entries with
  | nil => exact laterP
  | cons first rest =>
      exact interleave_preserves P value suffix first _ valueP suffixP
        (entriesP first List.mem_cons_self)
        (interleave_fold_preserves P value suffix rest later valueP suffixP
          (fun chosen member => entriesP chosen (List.mem_cons.mpr (.inr member))) laterP)
termination_by entries.length

mutual
  /-- Every permutation in the exact source order retains the input property. -/
  theorem permutations_preserves (P : α → Prop) (values : List α)
      (inputs : ∀ x ∈ values, P x) :
      ∀ selected ∈ permutations values, ∀ x ∈ selected, P x := by
    intro selected member
    rw [permutations] at member
    rcases List.mem_cons.mp member with same | later
    · subst selected
      exact inputs
    · exact perms_preserves P values [] inputs (by intro x present; cases present) selected later
  termination_by (values.length, values.length + 1)
  decreasing_by all_goals simp_wf; omega

  /-- The source permutation worker retains both suffix and accumulated input properties. -/
  theorem perms_preserves (P : α → Prop) (suffix accumulated : List α)
      (suffixP : ∀ x ∈ suffix, P x) (accumulatedP : ∀ x ∈ accumulated, P x) :
      ∀ selected ∈ perms suffix accumulated, ∀ x ∈ selected, P x := by
    cases view : suffix with
    | nil =>
        intro selected member
        simp only [perms] at member
        cases member
    | cons first rest =>
        have currentP : ∀ x ∈ first :: rest, P x := by simpa only [view] using suffixP
        have firstP : P first := currentP first List.mem_cons_self
        have restP : ∀ x ∈ rest, P x := fun x member => currentP x (List.mem_cons.mpr (.inr member))
        have nextP : ∀ x ∈ first :: accumulated, P x := by
          intro x member
          rcases List.mem_cons.mp member with same | inside
          · subst x; exact firstP
          · exact accumulatedP x inside
        rw [perms]
        exact interleave_fold_preserves P first rest _ _ firstP restP
          (permutations_preserves P accumulated accumulatedP)
          (perms_preserves P rest (first :: accumulated) restP nextP)
  termination_by (suffix.length + accumulated.length, suffix.length)
  decreasing_by all_goals simp_wf; simp_all only [List.length_cons]; omega
end

/-- Every row in the literal finite selection table retains the original property. -/
theorem selections_preserves (P : String × α → Prop) (arguments : List (String × α))
    (inputs : ∀ x ∈ arguments, P x) :
    ∀ selected ∈ selections arguments, ∀ x ∈ selected, P x := by
  intro selected member
  obtain ⟨subset, inSubsequence, inPermutation⟩ := List.mem_flatMap.mp member
  exact permutations_preserves P subset
    (subsequences_preserves P arguments inputs subset inSubsequence) selected inPermutation

/-- Names-only last-winner lookup preserves properties of the actual original arguments. -/
theorem resolveSelection_preserves (P : String × α → Prop) (arguments : List (String × α))
    (names : List String) (winner : List (String × α))
    (inputs : ∀ x ∈ arguments, P x)
    (resolved : resolveSelection arguments names = some winner) : ∀ x ∈ winner, P x :=
  selections_preserves P arguments inputs winner (resolveSelection_spec arguments names winner resolved).1

/-- Every winning argument is an actual original argument, even with duplicate names. -/
theorem resolveSelection_subset (arguments : List (String × α)) (names : List String)
    (winner : List (String × α)) (resolved : resolveSelection arguments names = some winner) :
    ∀ x ∈ winner, x ∈ arguments :=
  resolveSelection_preserves (fun x => x ∈ arguments) arguments names winner (fun _ member => member) resolved

end MicroCFTA.SourceSynthesisSelectionOrigins
