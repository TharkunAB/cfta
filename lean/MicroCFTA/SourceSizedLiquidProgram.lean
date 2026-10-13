import MicroCFTA.SourceSizedLiquidLogical

/-!
# Ordered liquid evaluator effects

Query occurrences are separate external calls. They can return different
verdicts for the same query. Boolean evaluation stops at the source decisive
verdict. Raised solver exceptions propagate without conversion to Unknown.
-/

namespace MicroCFTA.SourceSizedLiquidProgram

open FullSyntax SourceGuards Guards SolverAdapter SourceGuardRefinement

/-- One actual SMT query includes its ordered fresh declarations. -/
structure Query where
  bindings : List (FullSyntax.Name × FullSyntax.Name)
  antecedent : Formula
  consequent : Formula

/-- Keep exceptions distinct while changing a returned verdict. -/
def mapResult (f : Verdict → Verdict) : Result → Result
  | .returned verdict => .returned (f verdict)
  | .raised err => .raised err

/-- Unknown identity suppresses a No result before source polarity is applied. -/
def reply (known positive : Bool) (verdict : Verdict) : Verdict :=
  polarize positive (match verdict with | .no => if known then .no else .unknown | other => other)

/-- Combine two completed verdicts using the selected Boolean operator. -/
def merge (conjunctive : Bool) (first second : Verdict) : Verdict :=
  if conjunctive then Guards.conjunction first second else Guards.disjunction first second

/-- The source decisive result stops the Boolean list immediately. -/
def stop (conjunctive : Bool) : Verdict := if conjunctive then .no else .yes

/-- A finite source evaluator program retains every query occurrence and Boolean order. -/
inductive Program where
  | done (verdict : Verdict)
  | query (request : Query) (known positive : Bool)
  | combine (conjunctive : Bool) (first rest : Program)

/-- Read the program with a fixed callback for comparison to the existing source model. -/
def evaluate (solver : Entailment Formula) : Program → Verdict
  | .done verdict => verdict
  | .query request known positive => reply known positive
      (solver request.bindings request.antecedent request.consequent)
  | .combine conjunctive first rest => merge conjunctive (evaluate solver first) (evaluate solver rest)

/-- Execute each query occurrence separately and preserve exception and short-circuit order. -/
inductive Run (oracle : Query → Nat → Result → Prop) : Program → Result → Nat → Prop where
  | done : Run oracle (.done verdict) (.returned verdict) 0
  | query : oracle request work result →
      Run oracle (.query request known positive) (mapResult (reply known positive) result) (work + 1)
  | raised : Run oracle first (.raised err) work →
      Run oracle (.combine conjunctive first rest) (.raised err) (work + 1)
  | stop : Run oracle first (.returned (stop conjunctive)) work →
      Run oracle (.combine conjunctive first rest) (.returned (stop conjunctive)) (work + 1)
  | next : Run oracle first (.returned verdict) work → verdict ≠ stop conjunctive →
      Run oracle rest result restWork →
      Run oracle (.combine conjunctive first rest) (mapResult (merge conjunctive verdict) result) (work + restWork + 1)

/-- A returned verdict may lose information; a raised exception asserts no verdict. -/
def ResultRefines : Result → Verdict → Prop
  | .returned actual, expected => Refines actual expected
  | .raised _, _ => True

/-- Scope masking and polarity preserve the verdict information order. -/
theorem reply_refines (known positive : Bool) (first second : Verdict) (refined : Refines first second) :
    Refines (reply known positive first) (reply known positive second) := by
  apply polarize_refines
  cases known <;> cases first <;> cases second <;> simp_all [Refines]

/-- Boolean combination preserves the verdict information order. -/
theorem merge_refines (conjunctive : Bool) (first second expectedFirst expectedSecond : Verdict)
    (left : Refines first expectedFirst) (right : Refines second expectedSecond) :
    Refines (merge conjunctive first second) (merge conjunctive expectedFirst expectedSecond) := by
  cases conjunctive
  · exact disjunction_refines _ _ _ _ left right
  · exact conjunction_refines _ _ _ _ left right

/-- An actual decisive head also decides the ideal Boolean result, without reading its tail. -/
theorem stop_refines (conjunctive : Bool) (expectedFirst expectedSecond : Verdict)
    (head : Refines (stop conjunctive) expectedFirst) :
    Refines (stop conjunctive) (merge conjunctive expectedFirst expectedSecond) := by
  cases conjunctive <;> cases expectedFirst <;> cases expectedSecond <;>
    simp_all [stop, merge, Refines, Guards.conjunction, Guards.disjunction]

/-- Per-occurrence oracle evidence is sufficient; no stable actual reply function is required. -/
theorem run_refines (oracle : Query → Nat → Result → Prop) (solver : Entailment Formula)
    (correct : ∀ request work result, oracle request work result →
      ResultRefines result (solver request.bindings request.antecedent request.consequent))
    {program result work} (run : Run oracle program result work) :
    ResultRefines result (evaluate solver program) := by
  induction run with
  | done => exact .inr rfl
  | @query request work result known positive called =>
      have evidence := correct request work result called
      cases result with
      | raised err => trivial
      | returned verdict => exact reply_refines known positive _ _ evidence
  | raised first ih => trivial
  | stop first ih => exact stop_refines _ _ _ ih
  | @next first verdict work conjunctive rest result restWork head notStopped tail ihHead ihTail =>
      cases result with
      | raised err => trivial
      | returned other => exact merge_refines _ _ _ _ _ ihHead ihTail

/-- A finite program has a completed result when every external call has one. -/
theorem finite_execution (oracle : Query → Nat → Result → Prop)
    (completed : ∀ request, ∃ work result, oracle request work result) (program : Program) :
    ∃ work result, Run oracle program result work := by
  induction program with
  | done verdict => exact ⟨0, .returned verdict, .done⟩
  | query request known positive =>
      obtain ⟨work, result, called⟩ := completed request
      exact ⟨work + 1, mapResult (reply known positive) result, .query called⟩
  | combine conjunctive first rest ihFirst ihRest =>
      obtain ⟨work, result, head⟩ := ihFirst
      cases result with
      | raised err => exact ⟨work + 1, .raised err, .raised head⟩
      | returned verdict =>
          by_cases decisive : verdict = stop conjunctive
          · subst verdict
            exact ⟨work + 1, .returned (stop conjunctive), .stop head⟩
          · obtain ⟨restWork, result, tail⟩ := ihRest
            exact ⟨work + restWork + 1, mapResult (merge conjunctive verdict) result, .next head decisive tail⟩

/-- Raised errs originate in an actual query occurrence, unchanged. -/
theorem raised_origin (oracle : Query → Nat → Result → Prop) {program result work}
    (run : Run oracle program result work) :
    ∀ err, result = .raised err → ∃ request work, oracle request work (.raised err) := by
  induction run with
  | done => intro err impossible; cases impossible
  | @query request work result known positive called =>
      intro err same
      cases result with
      | returned verdict => cases same
      | raised original => cases Result.raised.inj same; exact ⟨request, work, called⟩
  | raised head ih => exact ih
  | stop head ih => intro err impossible; cases impossible
  | @next first verdict work conjunctive rest result restWork head notStopped tail ihHead ihTail =>
      intro err same
      cases result with
      | returned other => cases same
      | raised original => cases Result.raised.inj same; exact ihTail _ rfl

end MicroCFTA.SourceSizedLiquidProgram
