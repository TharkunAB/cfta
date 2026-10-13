import MicroCFTA.SourceSizedLiquidEvaluation
import MicroCFTA.SourceSizedLiquidAdapter
import MicroCFTA.SourceSizedDecidedOperational

/-!
# Deriving Sized evaluator adequacy from liquid query evidence

The mathematical constraint meaning uses existing subtrees and logical
formula entailment. It does not test a solver answer. Each query occurrence
can return a different result. Only returned decided verdicts need evidence;
Unknown and raised exceptions retain their distinct control behavior.
-/

namespace MicroCFTA.SourceSizedLiquidAdequacy

open FullSyntax SourceFormula SourceObservations SourceSizedLiquidProgram
open SourceSizedLiquidEvaluation SourceSizedLiquidLogical SolverAdapter

/-- Normalized equality classes require existing equal subtrees at every stored path. -/
noncomputable def Equalities (constraint : SourceSymbolicIndex.Constraint Formula)
    (term : Language.Term (Label Formula)) : Prop :=
  match constraint.guard with
  | .bottom => False
  | _ => match SourceCompactGuards.sourceEqualities constraint with
      | none => False
      | some classes => ∀ paths ∈ classes, Symbolic.ClassSatisfied term paths

/-- The actual equality shortcut decides the independent path-class meaning. -/
theorem equalities_exact (constraint : SourceSymbolicIndex.Constraint Formula)
    (term : Language.Term (Label Formula)) :
    SourceSizedEqualities.constraintHolds constraint term = true ↔ Equalities constraint term := by
  unfold SourceSizedEqualities.constraintHolds Equalities
  split
  · simp_all
  · cases SourceCompactGuards.sourceEqualities constraint <;>
      simp [SourceSizedEqualities.equalitiesHold, List.all_eq_true, SourceSizedEqualities.classHolds_exact]

/-- Full constraint satisfaction uses path equality and independent complete guard logic. -/
noncomputable def Logical (model : Interpretation Value)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) : Prop :=
  Equalities constraint term ∧ SourceQuotientGuards.Public model (fun _ _ => True) term true constraint.guard

/-- A classical Boolean view is used only as the semantic label of the mathematical graph. -/
noncomputable def truth (model : Interpretation Value)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) : Bool :=
  @decide (Logical model constraint term) (Classical.propDecidable _)

/-- No solver result occurs in the semantic graph label. -/
theorem truth_exact (model : Interpretation Value)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) :
    truth model constraint term = true ↔ Logical model constraint term := by
  simp [truth]

/-- Complete source constraint decisions derive their meaning from callback soundness. -/
theorem constraint_supports (model : Interpretation Value) (solver : SourceGuards.Entailment Formula)
    (sound : SourceEntailment.Sound model (fun _ _ => True) solver)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) :
    Guards.Supports (evaluateConstraint solver constraint term) (Logical model constraint term) := by
  unfold evaluateConstraint
  split
  next equalities =>
    have accepted := (equalities_exact constraint term).mp equalities
    exact supports_congr _ (by simp [Logical, accepted])
      (unrestricted_supports model solver sound constraint.guard term)
  next rejected =>
    exact fun valid => rejected ((equalities_exact constraint term).mpr valid.1)

/-- The ideal logical oracle is a proof comparison, not an implemented solver. -/
noncomputable def logicalSolver (model : Interpretation Value) : SourceGuards.Entailment Formula := by
  classical
  exact fun _ antecedent consequent =>
    if SourceEntailment.Entails model (fun _ => True) antecedent consequent then .yes else .no

/-- The comparison oracle directly satisfies the independent entailment judgment. -/
theorem logicalSolver_sound (model : Interpretation Value) :
    SourceEntailment.Sound model (fun _ _ => True) (logicalSolver model) := by
  intro bindings antecedent consequent
  unfold logicalSolver
  split <;> assumption

/-- A per-occurrence query contract states mathematical evidence only for returned decisions. -/
def QuerySound (model : Interpretation Value) (oracle : Query → Nat → Result → Prop) : Prop :=
  ∀ query work result, oracle query work result →
    ResultSupports result (SourceEntailment.Entails model (fun _ => True) query.antecedent query.consequent)

/-- Per-query evidence refines the ideal oracle even when repeated actual replies differ. -/
theorem query_refines (model : Interpretation Value) (oracle : Query → Nat → Result → Prop)
    (sound : QuerySound model oracle) (query : Query) (work : Nat) (result : Result)
    (called : oracle query work result) :
    ResultRefines result ((logicalSolver model) query.bindings query.antecedent query.consequent) := by
  have evidence := sound query work result called
  cases result with
  | raised err => trivial
  | returned verdict =>
      cases verdict with
      | unknown => exact .inl rfl
      | yes =>
          exact .inr (by simp [logicalSolver, show SourceEntailment.Entails model (fun _ => True)
            query.antecedent query.consequent from evidence])
      | no => exact .inr (by simp [logicalSolver, show ¬SourceEntailment.Entails model (fun _ => True)
            query.antecedent query.consequent from evidence])

/-- Every actual constraint trace supports its independent meaning, including nested scopes. -/
theorem run_supports (model : Interpretation Value) (oracle : Query → Nat → Result → Prop)
    (sound : QuerySound model oracle) (constraint : SourceSymbolicIndex.Constraint Formula)
    (term : Language.Term (Label Formula)) {result work}
    (run : Run oracle (constraintProgram constraint term) result work) :
    ResultSupports result (Logical model constraint term) := by
  have refined := run_refines oracle (logicalSolver model) (query_refines model oracle sound) run
  rw [constraint_source] at refined
  have evidence := constraint_supports model (logicalSolver model) (logicalSolver_sound model) constraint term
  cases result with
  | raised err => trivial
  | returned verdict =>
      rcases refined with unknown | same
      · subst verdict; trivial
      · simpa only [same, ResultSupports] using evidence

/-- A returned complete constraint evaluation is one source program trace. -/
def Evaluates (oracle : Query → Nat → Result → Prop)
    (pair : SourceSymbolicIndex.Constraint Formula × Language.Term (Label Formula))
    (work : Nat) (verdict : Guards.Verdict) : Prop :=
  Run oracle (constraintProgram pair.1 pair.2) (.returned verdict) work

/-- The Sized per-call adequacy premise follows from actual liquid query evidence. -/
theorem sized_adequate (model : Interpretation Value) (oracle : Query → Nat → Result → Prop)
    (sound : QuerySound model oracle) :
    SourceSizedDecidedOperational.Adequate (Evaluates oracle) (fun pair => truth model pair.1 pair.2) := by
  intro pair work verdict executed
  exact supports_congr verdict (truth_exact model pair.1 pair.2).symm
    (run_supports model oracle sound pair.1 pair.2 executed)

/-- A finite program has a returned result when each query has a finite returned result. -/
theorem finite_returned (oracle : Query → Nat → Result → Prop)
    (completed : ∀ query, ∃ work verdict, oracle query work (.returned verdict)) (program : Program) :
    ∃ work verdict, Run oracle program (.returned verdict) work := by
  induction program with
  | done verdict => exact ⟨0, verdict, .done⟩
  | query request known positive =>
      obtain ⟨work, verdict, called⟩ := completed request
      exact ⟨work + 1, reply known positive verdict, .query called⟩
  | combine conjunctive first rest ihFirst ihRest =>
      obtain ⟨work, verdict, head⟩ := ihFirst
      by_cases decisive : verdict = stop conjunctive
      · subst verdict
        exact ⟨work + 1, stop conjunctive, .stop head⟩
      · obtain ⟨restWork, other, tail⟩ := ihRest
        exact ⟨work + restWork + 1, merge conjunctive verdict other, .next head decisive tail⟩

/-- Finite returned query witnesses derive the Sized completion premise; raised exceptions are excluded explicitly. -/
theorem sized_terminates (oracle : Query → Nat → Result → Prop)
    (completed : ∀ query, ∃ work verdict, oracle query work (.returned verdict)) :
    SourceSizedDecidedOperational.Terminates (Evaluates oracle) := by
  intro pair
  exact finite_returned oracle completed (constraintProgram pair.1 pair.2)

/-- The actual all-Int adapter derives Sized adequacy from only correct external Sat and Unsat responses. -/
theorem adapter_adequate (model : FormulaLowering.Model Value)
    (allInteger : ∀ value, model.hasSort .int value)
    (given : List Declaration) (integer : SourceReadLogicalIntegerAdapter.IntegerDeclarations given)
    (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response) :
    SourceSizedDecidedOperational.Adequate (Evaluates (SourceSizedLiquidAdapter.Call given milliseconds check))
      (fun pair => truth (FormulaLowering.sourceModel model) pair.1 pair.2) :=
  sized_adequate (FormulaLowering.sourceModel model) _
    (fun _ _ _ called => SourceSizedLiquidAdapter.call_supports model allInteger given integer milliseconds check correct called)

end MicroCFTA.SourceSizedLiquidAdequacy
