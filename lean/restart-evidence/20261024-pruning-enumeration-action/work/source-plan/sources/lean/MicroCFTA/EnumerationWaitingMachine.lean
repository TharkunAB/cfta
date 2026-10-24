import MicroCFTA.EnumerationWaitingIndex
import Init.Data.BitVec.Lemmas

/-!
# Machine counters for the cached waiting index

The source uses signed Int counters. Bounds on the actual full scan before
and after a replacement bound every intermediate decrement and increment.
These bounds make all word updates equal to the integer index model.
-/
namespace MicroCFTA.EnumerationWaitingMachine
open EnumerationState EnumerationSchedule EnumerationWaitingIndex

/-- The source addition reads the signed result of machine-word addition. -/
def wordAdd (bits : Nat) (left right : Int) : Int :=
  (BitVec.ofInt (bits + 1) left + BitVec.ofInt (bits + 1) right).toInt

/-- A nonnegative sum below the signed limit has its exact machine result. -/
theorem wordAdd_exact (bits : Nat) (left right : Int)
    (nonnegative : 0 ≤ left + right) (bounded : left + right < (2 : Int) ^ bits) :
    wordAdd bits left right = left + right := by
  rw [wordAdd, ← BitVec.ofInt_add]
  apply BitVec.toInt_ofInt_eq_self (by omega)
  · simp only [Nat.add_sub_cancel]
    have positive : 0 < (2 : Int) ^ bits := Int.pow_pos (by decide)
    omega
  · simpa using bounded

/-- One source sparse-map mutation uses signed addition before zero deletion. -/
def bumpWord (bits : Nat) (change : Int) (uv : Nat) (waiting : Waiting) : Waiting :=
  fun other => if other = uv then encode (wordAdd bits (read waiting uv) change) else waiting other

/-- A bounded source update agrees exactly with the integer sparse-map operation. -/
theorem bumpWord_exact (bits : Nat) (change : Int) (uv : Nat) (waiting : Waiting)
    (nonnegative : 0 ≤ read waiting uv + change) (bounded : read waiting uv + change < (2 : Int) ^ bits) :
    bumpWord bits change uv waiting = bump change uv waiting := by
  unfold bumpWord EnumerationWaitingIndex.bump
  rw [wordAdd_exact bits _ _ nonnegative bounded]

/-- Execute the source ordered fold using machine counter additions. -/
def countWord (bits : Nat) (change : Int) (scs : List Suspended) (waiting : Waiting) : Waiting :=
  scs.foldl (fun previous sc => bumpWord bits change sc.var previous) waiting

/-- Remaining occurrence counts suffice to bound every decrement in the old-slot fold. -/
theorem decrement_exact (bits : Nat) (scs : List Suspended) (waiting : Waiting)
    (bounds : ∀ uv, occurrences uv scs ≤ read waiting uv ∧ read waiting uv < (2 : Int) ^ bits) :
    countWord bits (-1) scs waiting = count (-1) scs waiting := by
  induction scs generalizing waiting with
  | nil => rfl
  | cons first rest ih =>
      have atFirst := bounds first.var
      have positive := occurrences_nonnegative first.var rest
      simp [occurrences] at atFirst
      have step := bumpWord_exact bits (-1) first.var waiting (by omega) (by omega)
      simp only [countWord, count, List.foldl_cons, step] at *
      apply ih
      intro uv
      have current := bounds uv
      rw [bump_read]
      by_cases same : first.var = uv
      · subst uv; simp [occurrences] at current ⊢; omega
      · simp [occurrences, same, Ne.symm same] at current ⊢; omega

/-- The final occurrence count bounds every increment in the new-slot fold. -/
theorem increment_exact (bits : Nat) (scs : List Suspended) (waiting : Waiting)
    (bounds : ∀ uv, 0 ≤ read waiting uv ∧ read waiting uv + occurrences uv scs < (2 : Int) ^ bits) :
    countWord bits 1 scs waiting = count 1 scs waiting := by
  induction scs generalizing waiting with
  | nil => rfl
  | cons first rest ih =>
      have atFirst := bounds first.var
      have positive := occurrences_nonnegative first.var rest
      simp [occurrences] at atFirst
      have step := bumpWord_exact bits 1 first.var waiting (by omega) (by omega)
      simp only [countWord, count, List.foldl_cons, step] at *
      apply ih
      intro uv
      have current := bounds uv
      rw [bump_read]
      by_cases same : first.var = uv
      · subst uv; simp [occurrences] at current ⊢; omega
      · simp [occurrences, same, Ne.symm same] at current ⊢; omega

/-- The source performs the complete removal before the complete addition. -/
def replaceWord (bits : Nat) (old new : UVarValue Symbol) (waiting : Waiting) : Waiting :=
  countWord bits 1 (references new) (countWord bits (-1) (references old) waiting)

/-- Bounds on the two actual slot scans derive exact machine replacement at every intermediate update. -/
theorem replaceWord_exact (bits : Nat) (values : List (UVarValue Symbol)) (index : Nat)
    (old new : UVarValue Symbol) (stored : values[index]? = some old)
    (waiting : Waiting) (correct : Correct values waiting)
    (beforeBound : ∀ uv, total uv values < (2 : Int) ^ bits)
    (afterBound : ∀ uv, total uv (values.set index new) < (2 : Int) ^ bits) :
    replaceWord bits old new waiting = replace old new waiting := by
  have removal (uv : Nat) := remove_nonnegative values index old stored waiting correct uv
  have subtract : countWord bits (-1) (references old) waiting = count (-1) (references old) waiting := by
    apply decrement_exact
    intro uv
    have lower := removal uv
    simp only [count_read, Int.neg_one_mul] at lower
    exact ⟨by omega, by rw [correct.facts.2 uv]; exact beforeBound uv⟩
  unfold replaceWord replace
  rw [subtract]
  apply increment_exact
  intro uv
  refine ⟨removal uv, ?_⟩
  have final := afterBound uv
  rw [total_set uv index values old new stored] at final
  simpa only [count_read, Int.neg_one_mul, correct.facts.2 uv, Int.sub_eq_add_neg] using final

/-- A bounded machine replacement retains the exact sparse waiting invariant. -/
theorem replaceWord_correct (bits : Nat) (values : List (UVarValue Symbol)) (index : Nat)
    (old new : UVarValue Symbol) (stored : values[index]? = some old)
    (waiting : Waiting) (correct : Correct values waiting)
    (beforeBound : ∀ uv, total uv values < (2 : Int) ^ bits)
    (afterBound : ∀ uv, total uv (values.set index new) < (2 : Int) ^ bits) :
    Correct (values.set index new) (replaceWord bits old new waiting) := by
  rw [replaceWord_exact bits values index old new stored waiting correct beforeBound afterBound]
  exact replace_correct values index old new stored waiting correct

end MicroCFTA.EnumerationWaitingMachine
