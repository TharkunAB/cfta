import Std

/-!
# A computed bound for deterministic subset discovery rounds

The source is the control flow of `Gen.Internal.Table.deterministicRows.go`.
It adds the fresh target keys, checks the limit, then stops if there is no
fresh key. Otherwise it calls `step` and continues. Each continuing round
adds at least one key. The nonnegative limit used by Sized is 1024.

The context can retain holders, transitions, and the current batch. This
control projection does not bound the work inside `step` or prove its row
invariants. The result has a bound on round count, not total tuple work.
-/
namespace MicroCFTA.SourceSizedDeterminizationDiscovery

variable {Key Context : Type} [DecidableEq Key]

/-- Retain each newly found key once, excluding keys from earlier rounds. -/
def fresh (known found : List Key) : List Key :=
  found.eraseDups.filter fun key => decide (key ∉ known)

/-- The finite discovery control can stop at the limit, finish, or exhaust its bound. -/
inductive Outcome (Key Context : Type) where
  | limitExceeded
  | ready (known : List Key) (context : Context)
  | exhausted

/-- Run the source limit and freshness checks before any bounded recursive call. -/
def run (limit : Nat) (step : List Key → List Key → Context → List Key × Context) :
    Nat → List Key → List Key → Context → Outcome Key Context
  | fuel, known, found, context =>
    let new := fresh known found
    let more := known ++ new
    if limit < more.length then .limitExceeded
    else if new = [] then .ready more context
    else match fuel with
      | 0 => .exhausted
      | remaining + 1 =>
        let next := step new more context
        run limit step remaining more next.1 next.2

/-- The unbounded source control records each limit or freshness check as one round. -/
inductive Evaluation (limit : Nat)
    (step : List Key → List Key → Context → List Key × Context) :
    List Key → List Key → Context → Nat → Outcome Key Context → Prop where
  | limit_exceeded (over : limit < (known ++ fresh known found).length) :
      Evaluation limit step known found context 1 .limitExceeded
  | done (within : (known ++ fresh known found).length ≤ limit)
      (empty : fresh known found = []) :
      Evaluation limit step known found context 1 (.ready (known ++ fresh known found) context)
  | next (within : (known ++ fresh known found).length ≤ limit)
      (nonempty : fresh known found ≠ [])
      (following : Evaluation limit step (known ++ fresh known found)
        (step (fresh known found) (known ++ fresh known found) context).1
        (step (fresh known found) (known ++ fresh known found) context).2 calls result) :
      Evaluation limit step known found context (calls + 1) result

/-- Every finite source evaluation stops without a bound-exhaustion result. -/
theorem Evaluation.terminal (limit : Nat)
    (step : List Key → List Key → Context → List Key × Context)
    (known found : List Key) (context : Context) (calls : Nat) (result : Outcome Key Context)
    (execution : Evaluation limit step known found context calls result) : result ≠ .exhausted := by
  induction execution with
  | limit_exceeded => intro h; cases h
  | done => intro h; cases h
  | next _ _ _ ih => exact ih

/-- Remaining capacity supplies enough recursion, with at most one final checking round. -/
theorem run_evaluates (limit : Nat)
    (step : List Key → List Key → Context → List Key × Context)
    (known found : List Key) (context : Context) (fuel : Nat)
    (enough : limit - known.length ≤ fuel) :
    ∃ calls, calls ≤ limit - known.length + 1 ∧
      Evaluation limit step known found context calls (run limit step fuel known found context) := by
  generalize remaining_eq : limit - known.length = remaining
  induction remaining using Nat.strongRecOn generalizing known found context fuel with
  | ind remaining ih =>
    by_cases over : limit < (known ++ fresh known found).length
    · refine ⟨1, by omega, ?_⟩
      cases fuel <;> simpa only [run, over, ↓reduceIte] using
        (Evaluation.limit_exceeded (step := step) (context := context) over)
    · have within : (known ++ fresh known found).length ≤ limit := by omega
      by_cases empty : fresh known found = []
      · refine ⟨1, by omega, ?_⟩
        cases fuel <;>
          (rw [run, ite_eq_right over, ite_eq_left empty]
           exact Evaluation.done within empty)
      · have positive : 0 < (fresh known found).length := by
          cases form : fresh known found with
          | nil => exact False.elim (empty form)
          | cons key rest => simp
        have longer : known.length < (known ++ fresh known found).length := by
          simp only [List.length_append]
          omega
        have smaller : limit - (known ++ fresh known found).length < remaining := by omega
        cases fuel with
        | zero => omega
        | succ fuel =>
          obtain ⟨calls, bounded, execution⟩ :=
            ih (limit - (known ++ fresh known found).length) smaller
              (known ++ fresh known found)
              (step (fresh known found) (known ++ fresh known found) context).1
              (step (fresh known found) (known ++ fresh known found) context).2 fuel
              (by omega) rfl
          refine ⟨calls + 1, by omega, ?_⟩
          simpa only [run, over, empty, ↓reduceIte] using
            (Evaluation.next within empty execution)

/-- The original limit computes the bound from the empty initial known set. -/
theorem complete (limit : Nat)
    (step : List Key → List Key → Context → List Key × Context)
    (initialFound : List Key) (context : Context) :
    ∃ calls, calls ≤ limit + 1 ∧
      Evaluation limit step [] initialFound context calls (run limit step limit [] initialFound context) ∧
      run limit step limit [] initialFound context ≠ .exhausted := by
  obtain ⟨calls, bound, execution⟩ := run_evaluates limit step [] initialFound context limit (by simp)
  exact ⟨calls, by simpa using bound, execution,
    execution.terminal limit step [] initialFound context calls _⟩

/-- Sized's 1024-key limit permits at most 1025 discovery-control rounds. -/
theorem sized_complete (step : List Key → List Key → Context → List Key × Context)
    (initialFound : List Key) (context : Context) :
    ∃ calls, calls ≤ 1025 ∧
      Evaluation 1024 step [] initialFound context calls (run 1024 step 1024 [] initialFound context) ∧
      run 1024 step 1024 [] initialFound context ≠ .exhausted :=
  complete 1024 step initialFound context

end MicroCFTA.SourceSizedDeterminizationDiscovery
