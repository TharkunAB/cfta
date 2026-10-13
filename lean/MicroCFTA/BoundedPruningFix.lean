import MicroCFTA.EqualityReduction

/-!
# The bounded source fixed-point caller

`fixWithin` performs no call when the signed budget is nonpositive. Each
positive round evaluates its function once. A stable round returns the old
value. An exhausted budget returns the last value, which need not be fixed.
A separate execution relation requires termination of each invoked step.
-/

namespace MicroCFTA.BoundedPruningFix

/-- Execute the source loop and count its completed function calls. -/
def run [DecidableEq α] (step : α → α) : Nat → α → α × Nat
  | 0, value => (value, 0)
  | rounds + 1, value =>
      let next := step value
      if next = value then (value, 1)
      else
        let result := run step rounds next
        (result.1, result.2 + 1)

/-- The signed source entry uses zero rounds for every nonpositive budget. -/
def fixWithin [DecidableEq α] (rounds : Int) (step : α → α) (value : α) : α :=
  (run step rounds.toNat value).1

/-- A nonpositive budget returns without applying the function. -/
theorem nonpositive [DecidableEq α] (rounds : Int) (step : α → α) (value : α)
    (empty : rounds ≤ 0) : fixWithin rounds step value = value := by
  simp [fixWithin, Int.toNat_eq_zero.mpr empty, run]

/-- The caller completes at most the number of calls in its budget. -/
theorem calls_le [DecidableEq α] (step : α → α) (rounds : Nat) (value : α) :
    (run step rounds value).2 ≤ rounds := by
  induction rounds generalizing value with
  | zero => simp [run]
  | succ rounds ih =>
      simp only [run]
      split
      · simp
      · exact Nat.succ_le_succ (ih (step value))

/-- Every invariant preserved by one completed call survives a bounded run. -/
theorem invariant [DecidableEq α] (step : α → α) (property : α → Prop)
    (preserved : ∀ value, property value → property (step value))
    (rounds : Nat) (value : α) (initial : property value) :
    property (run step rounds value).1 := by
  induction rounds generalizing value with
  | zero => exact initial
  | succ rounds ih =>
      simp only [run]
      split
      · exact initial
      · exact ih (step value) (preserved value initial)

/-- Bounded iteration preserves a meaning that each call preserves exactly. -/
theorem meaning_exact [DecidableEq α] (step : α → α) (meaning : α → Value → Prop)
    (preserved : ∀ value term, meaning (step value) term ↔ meaning value term)
    (rounds : Int) (value : α) (term : Value) :
    meaning (fixWithin rounds step value) term ↔ meaning value term := by
  apply invariant step (fun after => meaning after term ↔ meaning value term)
  · intro current same
    exact (preserved current term).trans same
  · exact Iff.rfl

/-- The result is fixed whenever the loop stops before it consumes its budget. -/
theorem early_stop_fixed [DecidableEq α] (step : α → α) (rounds : Nat) (value : α)
    (early : (run step rounds value).2 < rounds) :
    step (run step rounds value).1 = (run step rounds value).1 := by
  induction rounds generalizing value with
  | zero => simp [run] at early
  | succ rounds ih =>
      by_cases fixed : step value = value
      · simp only [run, fixed, ite_true]
      · simp only [run, fixed, ite_false] at early ⊢
        exact ih (step value) (by omega)

/-- A step evaluator terminates with the specified function result. -/
def Terminates (evaluates : α → Nat → α → Prop) (step : α → α) : Prop :=
  ∀ value, ∃ cost, evaluates value cost (step value)

/-- A finite source execution counts calls and their primitive evaluation costs. -/
inductive Execution (evaluates : α → Nat → α → Prop) (step : α → α) :
    Nat → α → α → Nat → Nat → Prop where
  | exhausted (value : α) : Execution evaluates step 0 value value 0 0
  | stable (rounds : Nat) (value : α) (cost : Nat)
      (completed : evaluates value cost (step value)) (fixed : step value = value) :
      Execution evaluates step (rounds + 1) value value 1 cost
  | changed (rounds : Nat) (value output : α) (cost calls tailCost : Nat)
      (completed : evaluates value cost (step value)) (different : step value ≠ value)
      (tail : Execution evaluates step rounds (step value) output calls tailCost) :
      Execution evaluates step (rounds + 1) value output (calls + 1) (cost + tailCost)

/-- A budget bounds completed calls even when individual call costs differ. -/
theorem execution_calls_le (evaluates : α → Nat → α → Prop) (step : α → α)
    (rounds : Nat) (value output : α) (calls cost : Nat)
    (finished : Execution evaluates step rounds value output calls cost) : calls ≤ rounds := by
  induction finished with
  | exhausted => omega
  | stable => omega
  | changed _ _ _ _ _ _ _ _ _ ih => omega

/-- A bounded loop has a finite execution when every invoked step terminates. -/
theorem finite_execution [DecidableEq α] (evaluates : α → Nat → α → Prop) (step : α → α)
    (terminates : Terminates evaluates step) (rounds : Nat) (value : α) :
    ∃ cost, Execution evaluates step rounds value (run step rounds value).1
      (run step rounds value).2 cost := by
  induction rounds generalizing value with
  | zero => exact ⟨0, .exhausted value⟩
  | succ rounds ih =>
      obtain ⟨cost, completed⟩ := terminates value
      by_cases fixed : step value = value
      · simpa only [run, fixed, ite_true] using
          Exists.intro cost (Execution.stable (evaluates := evaluates) (step := step) rounds value cost completed fixed)
      · obtain ⟨tailCost, tail⟩ := ih (step value)
        simpa only [run, fixed, ite_false] using
          Exists.intro (cost + tailCost)
            (Execution.changed rounds value (run step rounds (step value)).1 cost
              (run step rounds (step value)).2 tailCost completed fixed tail)

/-- Bounded equality narrowing keeps both original constraint sets and all their terms. -/
theorem equality_narrowing_exact [DecidableEq Node]
    (ops : EqualityReduction.Operations Node Symbol) (laws : EqualityReduction.Laws ops)
    (localClasses inherited : EqualityNormalize.Constraints)
    (active : EqualityNormalize.Active localClasses) (rounds : Int) (nodes : List Node)
    (term : Language.Term Symbol) :
    (EqualityReduction.Forest ops (fixWithin rounds (EqualityReduction.pass ops localClasses inherited) nodes) term ∧
      EqualityNormalize.Satisfies term localClasses ∧ EqualityNormalize.Satisfies term inherited) ↔
    EqualityReduction.Forest ops nodes term ∧ EqualityNormalize.Satisfies term localClasses ∧
      EqualityNormalize.Satisfies term inherited := by
  exact meaning_exact (EqualityReduction.pass ops localClasses inherited)
    (fun nodes term => EqualityReduction.Forest ops nodes term ∧
      EqualityNormalize.Satisfies term localClasses ∧ EqualityNormalize.Satisfies term inherited)
    (fun before term => EqualityReduction.constrained_pass_exact ops laws localClasses inherited active before term)
    rounds nodes term

/-- Exhaustion returns the last value even when the function has no fixed point. -/
theorem exhaustion_need_not_be_fixed :
    fixWithin 3 Nat.succ 0 = 3 ∧ Nat.succ (fixWithin 3 Nat.succ 0) ≠ fixWithin 3 Nat.succ 0 := by
  decide

end MicroCFTA.BoundedPruningFix
