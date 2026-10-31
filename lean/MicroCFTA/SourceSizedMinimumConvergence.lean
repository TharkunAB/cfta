import MicroCFTA.SourceSizedMinimumPass

/-!
# Finite comparison and actual signed pass descent

The comparison reads only the original finite state list.
A changed actual pass decreases the missing-key count or the signed sum.
The iteration starts from the empty table.
The pass preserves positive values before the sum is converted to Nat.
The resulting natural lexicographic measure makes the iteration total.
Map key order and structural minimum correctness remain separate.
-/
namespace MicroCFTA.SourceSizedMinimumConvergence
open SourceSizedMinimumPass
variable {Q Symbol Guard : Type}

/-- Compare table values in the supplied finite order. -/
def sameOn : List Q → Table Q → Table Q → Bool
  | [], _, _ => true
  | key :: rest, first, second =>
      decide (first key = second key) && sameOn rest first second

/-- Count states with no known value. -/
def missing : List Q → Table Q → Nat
  | [], _ => 0
  | key :: rest, known =>
      match known key with
      | none => missing rest known + 1
      | some _ => missing rest known

/-- Sum the known signed values in the original state sequence. -/
def signedMass : List Q → Table Q → Int
  | [], _ => 0
  | key :: rest, known =>
      match known key with
      | none => signedMass rest known
      | some value => value + signedMass rest known

private theorem sameOn_member (keys : List Q) (first second : Table Q) :
    sameOn keys first second = true → ∀ key, key ∈ keys → first key = second key := by
  induction keys with
  | nil => intro _ key member; cases member
  | cons head rest ih =>
      intro compared key member
      have parts : first head = second head ∧ sameOn rest first second = true := by
        simpa only [sameOn, Bool.and_eq_true, decide_eq_true_eq] using compared
      rcases List.mem_cons.mp member with atHead | inRest
      · simpa only [atHead] using parts.1
      · exact ih parts.2 key inRest

/-- The original complete finite carrier turns the computed comparison into full equality. -/
theorem sameOn_eq (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (first second : Table Q) (compared : sameOn input.states first second = true) :
    first = second := by
  funext key
  exact sameOn_member input.states first second compared key (input.complete key)

private theorem keys_progress [DecidableEq Q]
    (input : SourceSizedPreprocessing.Input Q Symbol Guard) (known : Table Q) (keys : List Q) :
    missing keys (pass input known) ≤ missing keys known ∧
    (missing keys (pass input known) = missing keys known →
      signedMass keys (pass input known) ≤ signedMass keys known) ∧
    (sameOn keys (pass input known) known = false →
      missing keys (pass input known) < missing keys known ∨
        missing keys (pass input known) = missing keys known ∧
          signedMass keys (pass input known) < signedMass keys known) := by
  induction keys with
  | nil => simp [missing, signedMass, sameOn]
  | cons key rest ih =>
      have missingBound := ih.1
      cases before : known key with
      | none =>
          cases after : pass input known key with
          | none => simpa [missing, signedMass, sameOn, before, after] using ih
          | some value =>
              simp only [missing, signedMass, before, after]
              refine ⟨by omega, ?_, ?_⟩
              · intro equalMissing
                omega
              · intro _changed
                exact Or.inl (by omega)
      | some old =>
          cases after : pass input known key with
          | none =>
              obtain ⟨value, actual, _bounded⟩ := pass_known input known key old before
              simp only [after, reduceCtorEq] at actual
          | some next =>
              have bounded : next ≤ old := by
                obtain ⟨value, actual, bound⟩ := pass_known input known key old before
                simp only [after, Option.some.injEq] at actual
                omega
              by_cases unchanged : next = old
              · subst next
                simpa [missing, signedMass, sameOn, before, after] using ih
              · have strictValue : next < old := by omega
                simp only [missing, signedMass, before, after]
                refine ⟨ih.1, ?_, ?_⟩
                · intro equalMissing
                  have tailBound := ih.2.1 equalMissing
                  omega
                · intro _changed
                  by_cases equalMissing : missing rest (pass input known) = missing rest known
                  · exact Or.inr ⟨equalMissing, by have tailBound := ih.2.1 equalMissing; omega⟩
                  · exact Or.inl (by have tailBound := ih.1; omega)

/-- The pair records the missing-key count and the signed known-value sum. -/
def signedMeasure (input : SourceSizedPreprocessing.Input Q Symbol Guard) (known : Table Q) : Nat × Int :=
  (missing input.states known, signedMass input.states known)

private theorem false_of_not_true (flag : Bool) (notTrue : ¬ flag = true) : flag = false := by
  cases flag
  · rfl
  · exact False.elim (notTrue rfl)

/-- The actual computable pass comparison produces equality or strict signed lexicographic loss. -/
theorem compare_pass [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (known : Table Q) :
    (sameOn input.states (pass input known) known = true ∧ pass input known = known) ∨
    (sameOn input.states (pass input known) known = false ∧
      Prod.Lex (fun a b : Nat => a < b) (fun a b : Int => a < b)
        (signedMeasure input (pass input known)) (signedMeasure input known)) := by
  by_cases compared : sameOn input.states (pass input known) known = true
  · exact Or.inl ⟨compared, sameOn_eq input _ _ compared⟩
  · have failed := false_of_not_true _ compared
    refine Or.inr ⟨failed, ?_⟩
    rcases (keys_progress input known input.states).2.2 failed with
      fewerMissing | ⟨sameMissing, smallerMass⟩
    · exact Prod.Lex.left _ _ fewerMissing
    · unfold signedMeasure
      rw [sameMissing]
      exact Prod.Lex.right _ smallerMass

private theorem mass_nonnegative (keys : List Q) (known : Table Q)
    (positive : ∀ current value, known current = some value → 0 < value) :
    0 ≤ signedMass keys known := by
  induction keys with
  | nil => exact Int.le_refl _
  | cons key rest ih =>
      cases found : known key with
      | none => simpa only [signedMass, found] using ih
      | some value =>
          have valuePositive := positive key value found
          simp only [signedMass, found]
          omega

/-- Positive actual tables use a natural measure with a well-founded order. -/
def naturalMeasure (input : SourceSizedPreprocessing.Input Q Symbol Guard) (known : Table Q) : Nat × Nat :=
  (missing input.states known, (signedMass input.states known).toNat)

private theorem natural_decrease [DecidableEq Q]
    (input : SourceSizedPreprocessing.Input Q Symbol Guard) (known : Table Q)
    (positive : ∀ current value, known current = some value → 0 < value)
    (changed : sameOn input.states (pass input known) known = false) :
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (naturalMeasure input (pass input known)) (naturalMeasure input known) := by
  have nextNonnegative := mass_nonnegative input.states (pass input known)
    (pass_positive input known positive)
  rcases (keys_progress input known input.states).2.2 changed with
    fewerMissing | ⟨sameMissing, smallerMass⟩
  · exact Prod.Lex.left _ _ fewerMissing
  · unfold naturalMeasure
    rw [sameMissing]
    apply Prod.Lex.right _
    omega

private structure Working (Q : Type) where
  known : Table Q
  positive : ∀ current value, known current = some value → 0 < value

private def settle [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (current : Working Q) : {done : Working Q // pass input done.known = done.known} :=
  if compared : sameOn input.states (pass input current.known) current.known = true then
    ⟨current, sameOn_eq input _ _ compared⟩
  else
    settle input ⟨pass input current.known, pass_positive input current.known current.positive⟩
termination_by naturalMeasure input current.known
decreasing_by
  exact natural_decrease input current.known current.positive (false_of_not_true _ compared)

/-- The original finite input computes the pass fixed point from the empty table. -/
def minimumSizes [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard) : Table Q :=
  (settle input ⟨fun _ => none, by intro current value impossible; cases impossible⟩).val.known

/-- The computed result is a positive fixed point with support in the original carrier. -/
theorem minimum_spec [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard) :
    pass input (minimumSizes input) = minimumSizes input ∧
      ∀ current value, minimumSizes input current = some value → current ∈ input.states ∧ 0 < value := by
  let initial : Working Q := ⟨fun _ => none, by intro current value impossible; cases impossible⟩
  let result := settle input initial
  change pass input result.val.known = result.val.known ∧
    ∀ current value, result.val.known current = some value → current ∈ input.states ∧ 0 < value
  refine ⟨result.property, ?_⟩
  intro current value found
  exact ⟨input.complete current, result.val.positive current value found⟩

end MicroCFTA.SourceSizedMinimumConvergence
