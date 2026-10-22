import MicroCFTA.Language

/-!
# Ordered short-circuit scans with actual callback state

A true continuation implements all. A false continuation implements any.
The range predicate checks only the next actual query and the suffixes
reached after a continuing callback. It does not assume callback completion.
-/
namespace MicroCFTA.SourceShortCircuitScan

/-- The source Boolean fold in left-to-right query order. -/
def fold (continueOn : Bool) (test : Query → Bool) : List Query → Bool
  | [] => continueOn
  | query :: rest => if test query = continueOn then fold continueOn test rest else !continueOn

/-- Continuing after true results is the source all scan. -/
theorem fold_all (test : Query → Bool) (queries : List Query) : fold true test queries = queries.all test := by
  induction queries with
  | nil => rfl
  | cons query rest ih => cases found : test query <;> simp [fold, found, ih]

/-- Continuing after false results is the source any scan. -/
theorem fold_any (test : Query → Bool) (queries : List Query) : fold false test queries = queries.any test := by
  induction queries with
  | nil => rfl
  | cons query rest ih => cases found : test query <;> simp [fold, found, ih]

/-- A finite source scan retains each executed callback and stops at the first decisive result. -/
inductive Run (continueOn : Bool) (step : Query → State → Bool → State → Prop) :
    List Query → State → Bool → State → Prop where
  | nil (state : State) : Run continueOn step [] state continueOn state
  | stop (first : step query state (!continueOn) after) : Run continueOn step (query :: rest) state (!continueOn) after
  | next (first : step query state continueOn middle) (tail : Run continueOn step rest middle result after) :
      Run continueOn step (query :: rest) state result after

/-- Word checks follow actual continuing callbacks and their reached suffixes. -/
def Ranges (continueOn : Bool) (step : Query → State → Bool → State → Prop) (allowed : Query → State → Prop) :
    List Query → State → Prop
  | [], _ => True
  | query :: rest, state => allowed query state ∧ ∀ after, step query state continueOn after → Ranges continueOn step allowed rest after

/-- Finite actual callbacks give finite exact ordered scans under reached-query range checks. -/
theorem complete (continueOn : Bool) (step : Query → State → Bool → State → Prop) (allowed : Query → State → Prop)
    (invariant : State → Prop) (test : Query → Bool)
    (callbacks : ∀ query state, invariant state → allowed query state →
      ∃ result after, step query state result after ∧ invariant after ∧ result = test query)
    (queries : List Query) (state : State) (valid : invariant state) (ranges : Ranges continueOn step allowed queries state) :
    ∃ result after, Run continueOn step queries state result after ∧ invariant after ∧ result = fold continueOn test queries := by
  induction queries generalizing state with
  | nil => exact ⟨continueOn, state, .nil state, valid, rfl⟩
  | cons query rest ih =>
      obtain ⟨observed, middle, first, middleValid, expected⟩ := callbacks query state valid ranges.1
      by_cases same : observed = continueOn
      · have continuing : step query state continueOn middle := by simpa only [same] using first
        obtain ⟨result, after, tail, afterValid, correct⟩ := ih middle middleValid (ranges.2 middle continuing)
        refine ⟨result, after, .next continuing tail, afterValid, ?_⟩
        simpa only [fold, expected.symm.trans same, ↓reduceIte] using correct
      · have other : observed = !continueOn := by cases observed <;> cases continueOn <;> simp_all
        refine ⟨!continueOn, middle, .stop (by simpa only [other] using first), middleValid, ?_⟩
        simp only [fold, ← expected, ite_eq_right same]

/-- Every actual completed scan has the reference Boolean and retained invariants when its callbacks do. -/
theorem Run.correct (continueOn : Bool) (step : Query → State → Bool → State → Prop) (allowed : Query → State → Prop)
    (invariant : State → Prop) (test : Query → Bool)
    (callbacks : ∀ query state, invariant state → allowed query state → ∀ result after,
      step query state result after → invariant after ∧ result = test query)
    {queries : List Query} {state after : State} {result : Bool} (execution : Run continueOn step queries state result after)
    (valid : invariant state) (ranges : Ranges continueOn step allowed queries state) :
    invariant after ∧ result = fold continueOn test queries := by
  induction execution with
  | nil state => exact ⟨valid, rfl⟩
  | @stop query state after rest first =>
      obtain ⟨retained, expected⟩ := callbacks query state valid ranges.1 (!continueOn) after first
      refine ⟨retained, ?_⟩
      simp only [fold, ← expected]
      cases continueOn <;> rfl
  | @next query state middle rest result after first tail ih =>
      obtain ⟨retained, expected⟩ := callbacks query state valid ranges.1 continueOn middle first
      obtain ⟨finalValid, exact⟩ := ih retained (ranges.2 middle first)
      refine ⟨finalValid, ?_⟩
      simpa only [fold, ← expected, ↓reduceIte] using exact

end MicroCFTA.SourceShortCircuitScan
