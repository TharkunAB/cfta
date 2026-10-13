import MicroCFTA.SourceSizedLiquidContext
import MicroCFTA.SourceSizedLiquidAmbientRepair

/-!
# Complete constraint adequacy in an ambient entailment context

The context meaning is independent of callback results. Each actual query
occurrence supplies its own evidence. The repaired mixed-sort adapter derives
that evidence from the declared external Sat and Unsat response contract.
-/

namespace MicroCFTA.SourceSizedLiquidAmbientAdequacy

open FullSyntax SourceObservations SourceSizedLiquidProgram SolverAdapter
open SourceSizedLiquidEvaluation SourceSizedLiquidLogical

/-- Path equality and complete guard logic define constraint satisfaction. -/
noncomputable def Logical (meaning : Query → Prop)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) : Prop :=
  SourceSizedLiquidAdequacy.Equalities constraint term ∧
    SourceSizedLiquidContext.Public meaning term true constraint.guard

/-- The mathematical graph label depends on logic alone. -/
noncomputable def truth (meaning : Query → Prop)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) : Bool :=
  @decide (Logical meaning constraint term) (Classical.propDecidable _)

/-- Logical constraint satisfaction is exactly its semantic graph label. -/
theorem truth_exact (meaning : Query → Prop)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) :
    truth meaning constraint term = true ↔ Logical meaning constraint term := by simp [truth]

/-- The complete source evaluator preserves the independent context meaning. -/
theorem constraint_supports (meaning : Query → Prop) (solver : SourceGuards.Entailment Formula)
    (sound : SourceSizedLiquidContext.Sound meaning solver)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) :
    Guards.Supports (evaluateConstraint solver constraint term) (Logical meaning constraint term) := by
  unfold evaluateConstraint
  split
  next equalities =>
    have accepted := (SourceSizedLiquidAdequacy.equalities_exact constraint term).mp equalities
    exact supports_congr _ (by simp [Logical, accepted])
      (SourceSizedLiquidContext.public_supports meaning solver sound term true constraint.guard)
  next rejected =>
    exact fun valid => rejected ((SourceSizedLiquidAdequacy.equalities_exact constraint term).mpr valid.1)

/-- A proof-only oracle decides the independent query meaning. -/
noncomputable def logicalSolver (meaning : Query → Prop) : SourceGuards.Entailment Formula := by
  classical
  exact fun bindings antecedent consequent => if meaning ⟨bindings, antecedent, consequent⟩ then .yes else .no

/-- The proof oracle has the required context certificate. -/
theorem logicalSolver_sound (meaning : Query → Prop) :
    SourceSizedLiquidContext.Sound meaning (logicalSolver meaning) := by
  intro bindings antecedent consequent
  unfold logicalSolver
  split <;> assumption

/-- Actual returned decisions have evidence in the independent query context. -/
def QuerySound (meaning : Query → Prop) (oracle : Query → Nat → Result → Prop) : Prop :=
  ∀ query work result, oracle query work result → ResultSupports result (meaning query)

/-- Occurrence-specific evidence refines the proof oracle without stable actual answers. -/
theorem query_refines (meaning : Query → Prop) (oracle : Query → Nat → Result → Prop)
    (sound : QuerySound meaning oracle) (query : Query) (work : Nat) (result : Result)
    (called : oracle query work result) :
    ResultRefines result ((logicalSolver meaning) query.bindings query.antecedent query.consequent) := by
  have evidence := sound query work result called
  cases result with
  | raised err => trivial
  | returned verdict =>
      cases verdict with
      | unknown => exact .inl rfl
      | yes => exact .inr (by simp [logicalSolver, show meaning query from evidence])
      | no => exact .inr (by simp [logicalSolver, show ¬meaning query from evidence])

/-- A constraint trace supports the complete context meaning, including every scope. -/
theorem run_supports (meaning : Query → Prop) (oracle : Query → Nat → Result → Prop)
    (sound : QuerySound meaning oracle) (constraint : SourceSymbolicIndex.Constraint Formula)
    (term : Language.Term (Label Formula)) {result work}
    (run : Run oracle (constraintProgram constraint term) result work) :
    ResultSupports result (Logical meaning constraint term) := by
  have refined := run_refines oracle (logicalSolver meaning) (query_refines meaning oracle sound) run
  rw [constraint_source] at refined
  have evidence := constraint_supports meaning (logicalSolver meaning) (logicalSolver_sound meaning) constraint term
  cases result with
  | raised err => trivial
  | returned verdict =>
      rcases refined with unknown | same
      · subst verdict; trivial
      · simpa only [same, ResultSupports] using evidence

/-- The Sized per-call guard contract follows from the actual query occurrences. -/
theorem sized_adequate (meaning : Query → Prop) (oracle : Query → Nat → Result → Prop)
    (sound : QuerySound meaning oracle) :
    SourceSizedDecidedOperational.Adequate (SourceSizedLiquidAdequacy.Evaluates oracle)
      (fun pair => truth meaning pair.1 pair.2) := by
  intro pair work verdict executed
  exact supports_congr verdict (truth_exact meaning pair.1 pair.2).symm
    (run_supports meaning oracle sound pair.1 pair.2 executed)

/-- The repaired adapter derives guard adequacy with arbitrary ambient sorts and assumptions. -/
theorem adapter_adequate (model : FormulaLowering.Model Value)
    (given : List Declaration) (assumptions : List Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop)
    (correct : ∀ request work response reached, check request work (.answered response reached) →
      ResponseCorrect model request response) :
    SourceSizedDecidedOperational.Adequate
      (SourceSizedLiquidAdequacy.Evaluates (SourceSizedLiquidAmbientRepair.Call given assumptions milliseconds check))
      (fun pair => truth (SourceSizedLiquidAmbient.Meaning model given assumptions) pair.1 pair.2) :=
  sized_adequate _ _ (fun _ _ _ called =>
    SourceSizedLiquidAmbientRepair.call_supports model given assumptions milliseconds check correct called)

end MicroCFTA.SourceSizedLiquidAmbientAdequacy
