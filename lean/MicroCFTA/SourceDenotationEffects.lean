import MicroCFTA.SourceSizedLiquidExecution

/-!
# Ordered residual checks in bounded denotation

Each enumerated run contains a term and its ordered residual obligations.
The source andM stops at the first No. Unknown and external exceptions stop
the whole filter. Deduplication occurs only after every retained run has
finished. Repeated obligations remain separate evaluator occurrences.
-/

namespace MicroCFTA.SourceDenotationEffects

open Guards SolverAdapter SourceSizedLiquidExecution

/-- The source residual conjunction stops before all later obligations after No or a failure. -/
inductive AllRun (evaluates : Item → Nat → SolverAdapter.Result → Prop) :
    List Item → Except (Halt Item) Bool → Nat → Prop where
  | nil : AllRun evaluates [] (.ok true) 0
  | unknown : evaluates item work (.returned .unknown) →
      AllRun evaluates (item :: rest) (.error (.unknown item)) (work + 1)
  | raised {failure : SolverAdapter.Failure} : evaluates item work (.raised failure) →
      AllRun evaluates (item :: rest) (.error (.raised failure)) (work + 1)
  | no : evaluates item work (.returned .no) → AllRun evaluates (item :: rest) (.ok false) (work + 1)
  | yes : evaluates item work (.returned .yes) → AllRun evaluates rest result tailWork →
      AllRun evaluates (item :: rest) result (work + tailWork + 1)

/-- The source filter retains successful runs in their original order. -/
inductive FilterRun (evaluates : Item → Nat → SolverAdapter.Result → Prop) :
    List (Value × List Item) → Except (Halt Item) (List (Value × List Item)) → Nat → Prop where
  | nil : FilterRun evaluates [] (.ok []) 0
  | error : AllRun evaluates row.2 (.error bad) work →
      FilterRun evaluates (row :: rest) (.error bad) (work + 1)
  | no : AllRun evaluates row.2 (.ok false) work → FilterRun evaluates rest result tailWork →
      FilterRun evaluates (row :: rest) result (work + tailWork + 1)
  | yesOk : AllRun evaluates row.2 (.ok true) work → FilterRun evaluates rest (.ok kept) tailWork →
      FilterRun evaluates (row :: rest) (.ok (row :: kept)) (work + tailWork + 1)
  | yesError : AllRun evaluates row.2 (.ok true) work → FilterRun evaluates rest (.error bad) tailWork →
      FilterRun evaluates (row :: rest) (.error bad) (work + tailWork + 1)

/-- Every used returned decision supports its independent predicate. -/
def Adequate (evaluates : Item → Nat → SolverAdapter.Result → Prop) (holds : Item → Bool) : Prop :=
  ∀ item work verdict, evaluates item work (.returned verdict) → Supports verdict (holds item = true)

/-- A completed Boolean check equals conjunction of the actual obligation meanings. -/
theorem all_success (evaluates : Item → Nat → SolverAdapter.Result → Prop) (holds : Item → Bool)
    (adequate : Adequate evaluates holds) {items result work} (run : AllRun evaluates items result work) :
    ∀ accepted, result = .ok accepted → accepted = items.all holds := by
  induction run with
  | nil => intro accepted same; cases same; rfl
  | unknown called => intro accepted impossible; cases impossible
  | raised called => intro accepted impossible; cases impossible
  | @no item work rest called =>
      intro accepted same
      cases same
      have rejected := adequate item work .no called
      simp [Bool.eq_false_iff.mpr rejected]
  | @yes item work rest result tailWork called tail ih =>
      intro accepted same
      have valid : holds item = true := adequate item work .yes called
      simpa [valid] using ih accepted same

/-- A completed filter is exactly the semantic subsequence, including its order and duplicates. -/
theorem filter_success (evaluates : Item → Nat → SolverAdapter.Result → Prop) (holds : Item → Bool)
    (adequate : Adequate evaluates holds) {rows : List (Value × List Item)} {result work} (run : FilterRun evaluates rows result work) :
    ∀ kept, result = .ok kept → kept = rows.filter (fun row => row.2.all holds) := by
  induction run with
  | nil => intro kept same; cases same; rfl
  | error failed => intro kept impossible; cases impossible
  | @no row work rest result tailWork rejected tail ih =>
      intro kept same
      have no := all_success evaluates holds adequate rejected false rfl
      simpa [← no] using ih kept same
  | @yesOk row work rest kept tailWork accepted tail ih =>
      intro output same
      cases same
      have yes := all_success evaluates holds adequate accepted true rfl
      simp [← yes, ih kept rfl]
  | yesError accepted tail ih => intro kept impossible; cases impossible

/-- Finite individual evaluations give a finite residual conjunction outcome. -/
theorem all_finite (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (completed : ∀ item, ∃ work result, evaluates item work result) (items : List Item) :
    ∃ result work, AllRun evaluates items result work := by
  induction items with
  | nil => exact ⟨.ok true, 0, .nil⟩
  | cons item rest ih =>
      obtain ⟨work, result, called⟩ := completed item
      cases result with
      | raised failure => exact ⟨.error (.raised failure), work + 1, .raised called⟩
      | returned verdict =>
          cases verdict with
          | unknown => exact ⟨.error (.unknown item), work + 1, .unknown called⟩
          | no => exact ⟨.ok false, work + 1, .no called⟩
          | yes =>
              obtain ⟨result, tailWork, tail⟩ := ih
              exact ⟨result, work + tailWork + 1, .yes called tail⟩

/-- A finite ordered run list has a finite outcome when every residual evaluation can finish. -/
theorem filter_finite (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    (completed : ∀ item, ∃ work result, evaluates item work result) (rows : List (Value × List Item)) :
    ∃ result work, FilterRun evaluates rows result work := by
  induction rows with
  | nil => exact ⟨.ok [], 0, .nil⟩
  | cons row rest ih =>
      obtain ⟨result, work, checked⟩ := all_finite evaluates completed row.2
      cases result with
      | error bad => exact ⟨.error bad, work + 1, .error checked⟩
      | ok value =>
          obtain ⟨result, tailWork, tail⟩ := ih
          cases value with
          | false => exact ⟨result, work + tailWork + 1, .no checked tail⟩
          | true => cases result with
              | error bad => exact ⟨.error bad, work + tailWork + 1, .yesError checked tail⟩
              | ok kept => exact ⟨.ok (row :: kept), work + tailWork + 1, .yesOk checked tail⟩

/-- The first failing obligation has a prefix consisting only of actual Yes decisions. -/
theorem all_first_stop (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    {items result work} (run : AllRun evaluates items result work) :
    ∀ bad, result = .error bad → ∃ before item after beforeWork stopWork,
      items = before ++ item :: after ∧ AllRun evaluates before (.ok true) beforeWork ∧
      Caused evaluates bad item stopWork := by
  induction run with
  | nil => intro bad impossible; cases impossible
  | unknown called => intro bad same; cases same; exact ⟨[], _, _, 0, _, rfl, .nil, rfl, called⟩
  | raised called => intro bad same; cases same; exact ⟨[], _, _, 0, _, rfl, .nil, called⟩
  | no called => intro bad impossible; cases impossible
  | @yes item work rest result tailWork called tail ih =>
      intro bad same
      obtain ⟨before, failed, after, beforeWork, stopWork, split, prior, cause⟩ := ih bad same
      exact ⟨item :: before, failed, after, work + beforeWork + 1, stopWork,
        by simp [split], .yes called prior, cause⟩

/-- The first failed run follows a completed source filter prefix. -/
theorem filter_first_stop (evaluates : Item → Nat → SolverAdapter.Result → Prop)
    {rows : List (Value × List Item)} {result work} (run : FilterRun evaluates rows result work) :
    ∀ bad, result = .error bad → ∃ before row after kept beforeWork stopWork,
      rows = before ++ row :: after ∧ FilterRun evaluates before (.ok kept) beforeWork ∧
      AllRun evaluates row.2 (.error bad) stopWork := by
  induction run with
  | nil => intro bad impossible; cases impossible
  | error failed => intro bad same; cases same; exact ⟨[], _, _, [], 0, _, rfl, .nil, failed⟩
  | @no row work rest result tailWork rejected tail ih =>
      intro bad same
      obtain ⟨before, failed, after, kept, beforeWork, stopWork, split, prior, cause⟩ := ih bad same
      exact ⟨row :: before, failed, after, kept, work + beforeWork + 1, stopWork,
        by simp [split], .no rejected prior, cause⟩
  | yesOk accepted tail ih => intro bad impossible; cases impossible
  | @yesError row work rest original tailWork accepted tail ih =>
      intro bad same
      obtain ⟨before, failed, after, kept, beforeWork, stopWork, split, prior, cause⟩ := ih bad same
      exact ⟨row :: before, failed, after, row :: kept, work + beforeWork + 1, stopWork,
        by simp [split], .yesOk accepted prior, cause⟩

end MicroCFTA.SourceDenotationEffects
