import MicroCFTA.SourceSizedLiquidProgram

/-!
# Per-occurrence Liquid Fixpoint adapter evidence

Preflight collisions return Unknown. Completed external checks keep the
source response mapping, including timeout and protocol exceptions. Each
query occurrence has its own result. The external semantic premise concerns
only Sat and Unsat for the actual prepared assertion.

The logical-domain bridge here uses an all-Int ambient declaration context
and no ambient assumptions. Mixed ambient sorts and nonempty assumptions
need a separate environment-domain bridge.
-/

namespace MicroCFTA.SourceSizedLiquidAdapter

open FullSyntax SolverAdapter SourceSizedLiquidProgram SourceReadLogicalIntegerAdapter

/-- One actual adapter call either fails preflight or executes one prepared external request. -/
inductive Call (given : List Declaration) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) : Query → Nat → Result → Prop where
  | preflight : prepareQuery given query.bindings [] query.antecedent query.consequent = none →
      Call given milliseconds check query 1 (.returned .unknown)
  | checked : prepareQuery given query.bindings [] query.antecedent query.consequent = some request →
      check request work attempt →
      Call given milliseconds check query (work + 1) (finish milliseconds attempt).result

/-- Prepared all-Int query domains are the unrestricted carrier under no ambient assumptions. -/
theorem entails_unrestricted (model : FormulaLowering.Model Value)
    (allInteger : ∀ value, model.hasSort .int value)
    (given : List Declaration) (integer : IntegerDeclarations given)
    (query : Query) (request : Prepared)
    (prepared : prepareQuery given query.bindings [] query.antecedent query.consequent = some request) :
    SolverAdapter.Entails model request.declared [] query.antecedent query.consequent ↔
      SourceEntailment.Entails (FormulaLowering.sourceModel model) (fun _ => True) query.antecedent query.consequent := by
  have declared := prepared_integer given integer query.bindings [] query.antecedent query.consequent request prepared
  constructor
  · intro entailed env _ assumed
    exact entailed env (admitted_integer model allInteger request.declared declared env) (by simp [holdsAll]) assumed
  · intro entailed env _ _ assumed
    exact entailed env trivial assumed

/-- Correct external responses derive per-call logical evidence; Unknown and exceptions assert nothing. -/
theorem call_supports (model : FormulaLowering.Model Value)
    (allInteger : ∀ value, model.hasSort .int value)
    (given : List Declaration) (integer : IntegerDeclarations given) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response)
    {query work result} (call : Call given milliseconds check query work result) :
    ResultSupports result (SourceEntailment.Entails (FormulaLowering.sourceModel model) (fun _ => True)
      query.antecedent query.consequent) := by
  cases call with
  | preflight rejected => trivial
  | @checked request work attempt query prepared called =>
      cases attempt with
      | interrupted description => trivial
      | answered response reached =>
          have support := response_sound model request [] query.antecedent query.consequent
            (prepared_assertion given query.bindings [] query.antecedent query.consequent request prepared)
            milliseconds reached response (correct request work response reached called)
          have same := entails_unrestricted model allInteger given integer query request prepared
          cases answer : responseVerdict milliseconds reached response with
          | raised err => simp only [finish, answer, ResultSupports]
          | returned verdict =>
              rw [answer] at support
              simpa only [finish, answer, ResultSupports] using
                SourceSizedLiquidLogical.supports_congr verdict same support

/-- Per-request completion gives a finite adapter result, including raised failures. -/
theorem call_finite (given : List Declaration) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (query : Query) :
    ∃ work result, Call given milliseconds check query work result := by
  cases prepared : prepareQuery given query.bindings [] query.antecedent query.consequent with
  | none => exact ⟨1, .returned .unknown, .preflight prepared⟩
  | some request =>
      obtain ⟨work, attempt, called⟩ := completed request
      exact ⟨work + 1, (finish milliseconds attempt).result, .checked prepared called⟩

/-- A returned Unknown before the time limit is an ordinary evaluator result. -/
theorem unknown_returned (given : List Declaration) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (query : Query) (request : Prepared) (work : Nat)
    (prepared : prepareQuery given query.bindings [] query.antecedent query.consequent = some request)
    (called : check request work (.answered .unknown false)) :
    Call given milliseconds check query (work + 1) (.returned .unknown) :=
  .checked prepared called

/-- A time-limit Unknown raises the source TimeLimitReached exception. -/
theorem timeout_raised (given : List Declaration) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (query : Query) (request : Prepared) (work : Nat)
    (prepared : prepareQuery given query.bindings [] query.antecedent query.consequent = some request)
    (called : check request work (.answered .unknown true)) :
    Call given milliseconds check query (work + 1) (.raised (.timeLimit milliseconds)) :=
  .checked prepared called

/-- A protocol Error response raises the original rejection instead of returning Unknown. -/
theorem rejected_raised (given : List Declaration) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (query : Query) (request : Prepared) (work : Nat)
    (message : String) (reached : Bool)
    (prepared : prepareQuery given query.bindings [] query.antecedent query.consequent = some request)
    (called : check request work (.answered (.error message) reached)) :
    Call given milliseconds check query (work + 1) (.raised (.rejected message)) :=
  .checked prepared called

end MicroCFTA.SourceSizedLiquidAdapter
