import MicroCFTA.SourceSizedLiquidAdequacy
import MicroCFTA.SourceSizedLiquidAmbient

/-!
# Complete guard logic in a declared ambient context

The query meaning supplies an environment domain and ambient assumptions.
Guard substitution changes its two formula operands and adds actual-value
assumptions. It does not change the surrounding ambient context. The guard
judgment is independent of solver replies and retains source polarity.
-/

namespace MicroCFTA.SourceSizedLiquidContext

open FullSyntax SourceFormula SourceObservations SourceQuotientEnvironment
open SourceSizedLiquidProgram SourceSizedLiquidLogical SourceSizedLiquidEvaluation
open SourceGuards (Guard Resolved)

/-- A logical scoped query names its exact declarations and substituted formula operands. -/
def scopedQuery (meaning : Query → Prop) (bindings : List (Name × Name)) (scopes : List Scope)
    (antecedent consequent : Formula) : Prop :=
  meaning ⟨(bindings ++ scopes.flatten.filterMap Resolved.declaration).eraseDups,
    SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent),
    SourceGuards.applySubstitutions operations scopes consequent⟩

/-- Declarative complete-guard satisfaction, parameterized by its ambient entailment context. -/
def Logical (meaning : Query → Prop) (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (scopes : List Scope) (positive : Bool) (inner : Guard Formula) : Prop :=
  match inner with
  | .top => positive = true
  | .bottom => positive = false
  | .same left right =>
      match observe term left, observe term right with
      | some _, some _ => sameTerm operations term scopes left right = some positive
      | _, _ => positive = false
  | .entails left right =>
      match observe term left, observe term right with
      | some a, some b => if positive then scopedQuery meaning [] scopes a.refinement b.refinement
          else ¬scopedQuery meaning [] scopes a.refinement b.refinement
      | _, _ => positive = false
  | .satisfies target requirement =>
      match observe term target with
      | some value => scopedQuery meaning [] scopes value.refinement
          (if positive then requirement else operations.negate requirement)
      | none => positive = false
  | .holds targets requirement =>
      match SourceGuards.observeMany (observe term) targets with
      | some values => scopedQuery meaning
          ((SourceGuards.contract operations targets values).1.map (fun name => (name, SourceGuards.valueName))) scopes
          (SourceGuards.contract operations targets values).2
          (if positive then requirement else operations.negate requirement)
      | none => positive = false
  | .substitute additions inner =>
      match SourceQuotientQueries.resolve term outer (sameTerm operations term []) additions with
      | some resolved => Logical meaning term outer (resolved :: scopes) positive inner
      | none => positive = false
  | .not inner => Logical meaning term outer scopes (!positive) inner
  | .and parts => if positive then ∀ part ∈ parts, Logical meaning term outer scopes positive part
      else ∃ part : {guard // guard ∈ parts}, Logical meaning term outer scopes positive part.val
  | .or parts => if positive then ∃ part : {guard // guard ∈ parts}, Logical meaning term outer scopes positive part.val
      else ∀ part ∈ parts, Logical meaning term outer scopes positive part
termination_by sizeOf inner
decreasing_by
  all_goals first | decreasing_tactic | (have bound := List.sizeOf_lt_of_mem part.property; simp_all only [SourceGuards.Guard.and.sizeOf_spec, SourceGuards.Guard.or.sizeOf_spec]; omega)

/-- Public Boolean operands retain independent complete actual-allocation contexts. -/
def Public (meaning : Query → Prop) (term : Language.Term (Label Formula)) (positive : Bool)
    (guard : Guard Formula) : Prop :=
  match guard with
  | .and parts => if positive then ∀ part ∈ parts, Public meaning term positive part
      else ∃ part : {guard // guard ∈ parts}, Public meaning term positive part.val
  | .or parts => if positive then ∃ part : {guard // guard ∈ parts}, Public meaning term positive part.val
      else ∀ part ∈ parts, Public meaning term positive part
  | .not inner => Public meaning term (!positive) inner
  | .substitute [] inner => Public meaning term positive inner
  | guard => Logical meaning term guard [] positive guard
termination_by sizeOf guard
decreasing_by
  all_goals first | decreasing_tactic | (have bound := List.sizeOf_lt_of_mem part.property; simp_all only [SourceGuards.Guard.and.sizeOf_spec, SourceGuards.Guard.or.sizeOf_spec]; omega)

/-- A mathematical query callback needs evidence only for its decided replies. -/
def Sound (meaning : Query → Prop) (solver : SourceGuards.Entailment Formula) : Prop :=
  ∀ bindings antecedent consequent, Guards.Supports (solver bindings antecedent consequent)
    (meaning ⟨bindings, antecedent, consequent⟩)

/-- Unknown-identity masking preserves every supplied query certificate. -/
theorem query_supports (meaning : Query → Prop) (solver : SourceGuards.Entailment Formula)
    (sound : Sound meaning solver) (bindings : List (Name × Name)) (scopes : List Scope)
    (antecedent consequent : Formula) :
    Guards.Supports (SourceGuards.decideWith solver bindings scopes
      (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent))
      (SourceGuards.applySubstitutions operations scopes consequent))
      (scopedQuery meaning bindings scopes antecedent consequent) := by
  have evidence := sound (bindings ++ scopes.flatten.filterMap Resolved.declaration).eraseDups
    (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent))
    (SourceGuards.applySubstitutions operations scopes consequent)
  unfold SourceGuards.decideWith
  dsimp only
  cases result : solver (bindings ++ scopes.flatten.filterMap Resolved.declaration).eraseDups
      (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent))
      (SourceGuards.applySubstitutions operations scopes consequent) with
  | unknown => trivial
  | yes => simpa only [result, scopedQuery] using evidence
  | no => simp only
          split
          · simpa only [result, scopedQuery] using evidence
          · trivial

/-- Complete scoped decisions support the independent guard meaning in any ambient query context. -/
theorem worker_supports (meaning : Query → Prop) (solver : SourceGuards.Entailment Formula)
    (sound : Sound meaning solver) (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (scopes : List Scope) (positive : Bool) (inner : Guard Formula) :
    Guards.Supports (SourceCompleteLogical.evaluate solver term outer scopes positive inner)
      (Logical meaning term outer scopes positive inner) := by
  cases inner with
  | top | bottom =>
      cases positive <;> simp [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, SourceGuards.polarize, Guards.negate, Logical, Guards.Supports]
  | same left right =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases leftFound : observe term left with
      | none => exact absence positive
      | some a => cases rightFound : observe term right with
        | none => exact absence positive
        | some b =>
            by_cases equal : left = right
            · subst right
              obtain ⟨subterm, found, _⟩ := Option.map_eq_some_iff.mp leftFound
              have reflexive := (Language.termEq_correct (renameTree operations scopes subterm) _).mpr rfl
              cases positive <;> simp [sameTerm, found, reflexive, SourceGuards.polarize, Guards.negate, Guards.Supports]
            · simp only [equal, ↓reduceIte]
              cases decided : sameTerm operations term scopes left right with
              | none => cases positive <;> simp [SourceGuards.polarize, Guards.negate, Guards.Supports]
              | some answer => cases positive <;> cases answer <;>
                  simp [SourceGuards.polarize, Guards.negate, Guards.Supports]
  | entails left right =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases observe term left with
      | none => exact absence positive
      | some a => cases observe term right with
        | none => exact absence positive
        | some b =>
            apply polarity
            exact query_supports meaning solver sound [] scopes a.refinement b.refinement
  | satisfies target requirement =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases observe term target with
      | none => exact absence positive
      | some value => exact query_supports meaning solver sound [] scopes value.refinement _
  | holds targets requirement =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases SourceGuards.observeMany (observe term) targets with
      | none => exact absence positive
      | some values => exact query_supports meaning solver sound _ scopes (SourceGuards.contract operations targets values).2 _
  | substitute additions inner =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases found : SourceQuotientQueries.resolve term outer (sameTerm operations term []) additions with
      | none =>
          have rawFound := found
          unfold SourceQuotientQueries.resolve at rawFound
          simpa only [rawFound] using absence positive
      | some scope =>
          have rawFound := found
          unfold SourceQuotientQueries.resolve at rawFound
          simp only [rawFound]
          split
          · trivial
          · exact worker_supports meaning solver sound term outer (scope :: scopes) positive inner
  | not inner =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      exact worker_supports meaning solver sound term outer scopes (!positive) inner
  | and parts | or parts =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals first | apply conjunction | apply disjunction
      all_goals
        intro part member
        exact worker_supports meaning solver sound term outer scopes _ part
termination_by sizeOf inner

/-- Public complete decisions retain the same context while each Boolean operand allocates independently. -/
theorem public_supports (meaning : Query → Prop) (solver : SourceGuards.Entailment Formula)
    (sound : Sound meaning solver) (term : Language.Term (Label Formula))
    (positive : Bool) (guard : Guard Formula) :
    Guards.Supports (SourceSubstitutionPrecedence.evaluate operations solver (observe term) (sameTerm operations term) positive guard)
      (Public meaning term positive guard) := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [SourceSubstitutionPrecedence.evaluate, Public]
      exact worker_supports meaning solver sound term _ [] positive _
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [SourceSubstitutionPrecedence.evaluate, Public]
          exact public_supports meaning solver sound term positive inner
      | cons first rest =>
          simp only [SourceSubstitutionPrecedence.evaluate, Public]
          exact worker_supports meaning solver sound term _ [] positive _
  | not inner =>
      simp only [SourceSubstitutionPrecedence.evaluate, Public]
      exact public_supports meaning solver sound term (!positive) inner
  | and parts | or parts =>
      simp only [SourceSubstitutionPrecedence.evaluate, Public]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals first | apply conjunction | apply disjunction
      all_goals
        intro part member
        exact public_supports meaning solver sound term _ part
termination_by sizeOf guard

end MicroCFTA.SourceSizedLiquidContext
