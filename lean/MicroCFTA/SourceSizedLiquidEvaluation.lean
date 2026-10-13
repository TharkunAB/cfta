import MicroCFTA.SourceSizedLiquidProgram
import MicroCFTA.SourceSizedEqualities

/-!
# Complete source liquid evaluation as an ordered query program

The program retains each query, actual assumption, fresh declaration,
substitution scope, and Boolean short circuit. Its fixed-callback reading
equals the existing complete source evaluator. Its operational reading can
use different external replies at each occurrence.
-/

namespace MicroCFTA.SourceSizedLiquidEvaluation

open FullSyntax SourceFormula SourceObservations SourceQuotientEnvironment
open SourceGuards (Guard Resolved)
open SourceSizedLiquidProgram

/-- Preserve the source Boolean list order and its empty-list verdict. -/
def listProgram (conjunctive : Bool) (programs : List Program) : Program :=
  programs.foldr (.combine conjunctive) (.done (if conjunctive then .yes else .no))

/-- The program list has exactly the existing source verdict fold. -/
theorem evaluate_list (solver : SourceGuards.Entailment Formula) (conjunctive : Bool)
    (programs : List Program) :
    evaluate solver (listProgram conjunctive programs) =
      SourceGuards.combine conjunctive (programs.map (evaluate solver)) := by
  induction programs with
  | nil => rfl
  | cons first rest ih =>
      simp only [listProgram, List.foldr_cons, evaluate, List.map_cons,
        SourceGuardRefinement.combine_cons]
      rw [show evaluate solver (List.foldr (Program.combine conjunctive)
        (Program.done (if conjunctive then .yes else .no)) rest) = _ from ih]
      rfl

/-- A query preserves ordered declarations, unknown-identity masking, and polarity. -/
def queryProgram (bindings : List (Name × Name)) (scopes : List Scope) (positive : Bool)
    (antecedent consequent : Formula) : Program :=
  .query ⟨(bindings ++ scopes.flatten.filterMap Resolved.declaration).eraseDups, antecedent, consequent⟩
    (scopes.all (fun scope => scope.all Resolved.identityKnown)) positive

/-- A query program reads exactly the source decideWith callback. -/
theorem evaluate_query (solver : SourceGuards.Entailment Formula)
    (bindings : List (Name × Name)) (scopes : List Scope) (positive : Bool)
    (antecedent consequent : Formula) :
    evaluate solver (queryProgram bindings scopes positive antecedent consequent) =
      SourceGuards.polarize positive (SourceGuards.decideWith solver bindings scopes antecedent consequent) := rfl

/-- Retain one complete actual-allocation context through every nested scope. -/
def scopeProgram (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (scopes : List Scope) (positive : Bool) : Guard Formula → Program
  | .top => .done (SourceGuards.polarize positive .yes)
  | .bottom => .done (SourceGuards.polarize positive .no)
  | .same left right => .done (match observe term left, observe term right with
      | some _, some _ => SourceGuards.polarize positive (if left = right then .yes else
          match sameTerm operations term scopes left right with
          | some true => .yes | some false => .no | none => .unknown)
      | _, _ => SourceGuards.absent positive)
  | .entails left right =>
      match observe term left, observe term right with
      | some a, some b => queryProgram [] scopes positive
          (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes a.refinement))
          (SourceGuards.applySubstitutions operations scopes b.refinement)
      | _, _ => .done (SourceGuards.absent positive)
  | .satisfies target requirement =>
      match observe term target with
      | some value => queryProgram [] scopes true
          (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes value.refinement))
          (SourceGuards.applySubstitutions operations scopes (if positive then requirement else operations.negate requirement))
      | none => .done (SourceGuards.absent positive)
  | .holds targets requirement =>
      match SourceGuards.observeMany (observe term) targets with
      | some values => queryProgram ((SourceGuards.contract operations targets values).1.map
          (fun name => (name, SourceGuards.valueName))) scopes true
          (SourceGuards.withActualAssumptions operations scopes
            (SourceGuards.applySubstitutions operations scopes (SourceGuards.contract operations targets values).2))
          (SourceGuards.applySubstitutions operations scopes (if positive then requirement else operations.negate requirement))
      | none => .done (SourceGuards.absent positive)
  | .substitute additions inner =>
      match SourceQuotientQueries.resolve term outer (sameTerm operations term []) additions with
      | none => .done (SourceGuards.absent positive)
      | some scope =>
          if scope.any (SourceEnclosingRenames.renamedByEnclosing scopes) ||
              SourceSubstitutionPrecedence.ambiguousIdentityPrecedence scope then .done .unknown
          else scopeProgram term outer (scope :: scopes) positive inner
  | .not inner => scopeProgram term outer scopes (!positive) inner
  | .and parts => listProgram positive (parts.map (scopeProgram term outer scopes positive))
  | .or parts => listProgram (!positive) (parts.map (scopeProgram term outer scopes positive))

/-- The complete scopeProgram query program is the actual source worker, including rejected scopes. -/
theorem scoped_source (solver : SourceGuards.Entailment Formula)
    (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (scopes : List Scope) (positive : Bool) (inner : Guard Formula) :
    evaluate solver (scopeProgram term outer scopes positive inner) =
      SourceCompleteLogical.evaluate solver term outer scopes positive inner := by
  cases inner with
  | top | bottom =>
      simp only [scopeProgram, evaluate, SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith]
  | same left right =>
      simp only [scopeProgram, evaluate, SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith]
      cases observe term left <;> cases observe term right <;> rfl
  | entails left right =>
      simp only [scopeProgram, SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith]
      cases observe term left <;> cases observe term right <;> simp [evaluate, evaluate_query]
  | satisfies target requirement =>
      simp only [scopeProgram, SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith]
      cases observe term target <;> simp [evaluate, evaluate_query, SourceGuards.polarize]
  | holds targets requirement =>
      simp only [scopeProgram, SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith]
      cases SourceGuards.observeMany (observe term) targets <;>
        simp [evaluate, evaluate_query, SourceGuards.polarize]
  | substitute additions inner =>
      simp only [scopeProgram, SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith]
      cases found : SourceQuotientQueries.resolve term outer (sameTerm operations term []) additions with
      | none =>
          unfold SourceQuotientQueries.resolve at found
          simp only [found, evaluate]
      | some scope =>
          have raw := found
          unfold SourceQuotientQueries.resolve at raw
          simp only [raw]
          split
          · rfl
          · exact scoped_source solver term outer (scope :: scopes) positive inner
  | not inner =>
      simpa only [scopeProgram, SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith] using scoped_source solver term outer scopes (!positive) inner
  | and parts | or parts =>
      simp only [scopeProgram, evaluate_list, List.map_map, Function.comp_def,
        SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith]
      congr 1
      apply List.map_congr_left
      intro part member
      exact scoped_source solver term outer scopes positive part
termination_by sizeOf inner

/-- Public Boolean operands allocate their complete actual tables independently. -/
def guardProgram (term : Language.Term (Label Formula)) (positive : Bool) : Guard Formula → Program
  | .and parts => listProgram positive (parts.map (guardProgram term positive))
  | .or parts => listProgram (!positive) (parts.map (guardProgram term positive))
  | .not inner => guardProgram term (!positive) inner
  | .substitute [] inner => guardProgram term positive inner
  | guard => scopeProgram term guard [] positive guard

/-- The public program reading agrees with the current complete source evaluator. -/
theorem guard_source (solver : SourceGuards.Entailment Formula)
    (term : Language.Term (Label Formula)) (positive : Bool) (guard : Guard Formula) :
    evaluate solver (guardProgram term positive guard) =
      SourceSubstitutionPrecedence.evaluate operations solver (observe term) (sameTerm operations term) positive guard := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [guardProgram, SourceSubstitutionPrecedence.evaluate]
      exact scoped_source solver term _ [] positive _
  | substitute additions inner =>
      cases additions with
      | nil =>
          simpa only [guardProgram, SourceSubstitutionPrecedence.evaluate] using guard_source solver term positive inner
      | cons first rest =>
          simp only [guardProgram, SourceSubstitutionPrecedence.evaluate]
          exact scoped_source solver term _ [] positive _
  | not inner =>
      simpa only [guardProgram, SourceSubstitutionPrecedence.evaluate] using guard_source solver term (!positive) inner
  | and parts | or parts =>
      simp only [guardProgram, evaluate_list, List.map_map, Function.comp_def, SourceSubstitutionPrecedence.evaluate]
      congr 1
      apply List.map_congr_left
      intro part member
      exact guard_source solver term positive part
termination_by sizeOf guard

/-- The source rejects failed normalized equalities before evaluating any liquid guard. -/
noncomputable def evaluateConstraint (solver : SourceGuards.Entailment Formula)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) : Guards.Verdict :=
  if SourceSizedEqualities.constraintHolds constraint term then
    SourceSubstitutionPrecedence.evaluateGuard operations solver constraint.guard term else .no

/-- The complete source constraint becomes a finite ordered query program. -/
noncomputable def constraintProgram (constraint : SourceSymbolicIndex.Constraint Formula)
    (term : Language.Term (Label Formula)) : Program :=
  if SourceSizedEqualities.constraintHolds constraint term then guardProgram term true constraint.guard else .done .no

/-- Constraint programs include the source equality shortcut and current complete evaluator. -/
theorem constraint_source (solver : SourceGuards.Entailment Formula)
    (constraint : SourceSymbolicIndex.Constraint Formula) (term : Language.Term (Label Formula)) :
    evaluate solver (constraintProgram constraint term) = evaluateConstraint solver constraint term := by
  unfold constraintProgram evaluateConstraint
  split
  · exact guard_source solver term true constraint.guard
  · rfl

end MicroCFTA.SourceSizedLiquidEvaluation
