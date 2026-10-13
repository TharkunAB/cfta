import MicroCFTA.SourceCompleteLogical
import MicroCFTA.SourceReadLogicalIntegerAdapter

/-!
# Complete liquid guard decisions and independent logical satisfaction

Both Yes and No supply evidence for the complete term judgment. Scoped
substitution uses the actual complete allocation table. Negative Satisfies
and Holds query the negated formula. Negative Entails refutes entailment.
Unknown supplies no evidence in either direction.
-/

namespace MicroCFTA.SourceSizedLiquidLogical

open FullSyntax SourceFormula SourceObservations SourceQuotientEnvironment
open SourceQuotientQueries SourceQuotientGuards
open SourceGuards (Guard)

/-- Logical equivalence transports either decided verdict. -/
theorem supports_congr (verdict : Guards.Verdict) {first second : Prop}
    (same : first ↔ second) (evidence : Guards.Supports verdict first) :
    Guards.Supports verdict second := by
  cases verdict with
  | unknown => trivial
  | yes => exact same.mp evidence
  | no => exact fun accepted => evidence (same.mpr accepted)

/-- Ordinary Boolean polarity complements a decided proposition. -/
theorem polarity (positive : Bool) (verdict : Guards.Verdict) (claim : Prop)
    (support : Guards.Supports verdict claim) :
    Guards.Supports (SourceGuards.polarize positive verdict) (if positive then claim else ¬claim) := by
  cases positive <;> cases verdict <;> simp_all [SourceGuards.polarize, Guards.negate, Guards.Supports]

/-- A missing required path has the source polarity-dependent result. -/
theorem absence (positive : Bool) : Guards.Supports (SourceGuards.absent positive) (positive = false) := by
  cases positive <;> simp [SourceGuards.absent, Guards.Supports]

/-- Ordered conjunction preserves positive and negative logical evidence. -/
theorem conjunction (items : List α) (evaluate : α → Guards.Verdict) (claim : α → Prop)
    (sound : ∀ item ∈ items, Guards.Supports (evaluate item) (claim item)) :
    Guards.Supports (SourceGuards.combine true (items.map evaluate)) (∀ item ∈ items, claim item) := by
  cases verdict : SourceGuards.combine true (items.map evaluate) with
  | unknown => trivial
  | yes =>
      intro item member
      have chosen := (GuardConjunction.combine_yes _).mp verdict _ (List.mem_map.mpr ⟨item, member, rfl⟩)
      simpa only [chosen, Guards.Supports] using sound item member
  | no =>
      obtain ⟨item, member, chosen⟩ := List.mem_map.mp ((GuardConjunction.combine_no _).mp verdict)
      have refuted := sound item member
      rw [chosen] at refuted
      exact fun proved => refuted (proved item member)

/-- Ordered disjunction preserves positive and negative logical evidence. -/
theorem disjunction (items : List α) (evaluate : α → Guards.Verdict) (claim : α → Prop)
    (sound : ∀ item ∈ items, Guards.Supports (evaluate item) (claim item)) :
    Guards.Supports (SourceGuards.combine false (items.map evaluate)) (∃ item : {value // value ∈ items}, claim item.val) := by
  cases verdict : SourceGuards.combine false (items.map evaluate) with
  | unknown => trivial
  | yes =>
      obtain ⟨item, member, chosen⟩ := List.mem_map.mp ((GuardConjunction.disjoin_yes _).mp verdict)
      have proved := sound item member
      rw [chosen] at proved
      exact ⟨⟨item, member⟩, proved⟩
  | no =>
      rintro ⟨⟨item, member⟩, proved⟩
      have chosen := (GuardConjunction.disjoin_no _).mp verdict _ (List.mem_map.mpr ⟨item, member, rfl⟩)
      have refuted := sound item member
      rw [chosen] at refuted
      exact refuted proved

/-- Every complete scoped verdict supports the independent logical guard judgment. -/
theorem worker_supports (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term outer) solver)
    (scopes : List Scope) (positive : Bool) (inner : Guard Formula) :
    Guards.Supports (SourceCompleteLogical.evaluate solver term outer scopes positive inner)
      (Logical model sortDomain term outer scopes positive inner) := by
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
      cases leftFound : observe term left with
      | none => exact absence positive
      | some a => cases rightFound : observe term right with
        | none => exact absence positive
        | some b =>
            apply polarity
            exact SourceEntailment.decideWith_sound model (SolverDomain sortDomain term outer) solver sound [] scopes _ _
  | satisfies target requirement =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases found : observe term target with
      | none => exact absence positive
      | some value =>
          exact SourceEntailment.decideWith_sound model (SolverDomain sortDomain term outer) solver sound [] scopes _ _
  | holds targets requirement =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases found : SourceGuards.observeMany (observe term) targets with
      | none => exact absence positive
      | some values =>
          simp only []
          have bindings : (SourceGuards.contract operations targets values).1.map (fun name => (name, SourceGuards.valueName)) =
              (List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName)) := by
            simp [SourceGuards.contract, List.map_map, Function.comp_def]
          rw [bindings]
          have support := SourceEntailment.decideWith_sound model (SolverDomain sortDomain term outer) solver sound
            ((List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName))) scopes
            (SourceGuards.withActualAssumptions operations scopes
              (SourceGuards.applySubstitutions operations scopes (SourceGuards.contract operations targets values).2))
            (SourceGuards.applySubstitutions operations scopes (if positive then requirement else operations.negate requirement))
          apply supports_congr _ ?_ support
          simp only [SourceEntailment.Entails, SolverDomain, SourceQuotientHolds.Domain,
            SourceHoldsQueries.domain_exact]
  | substitute additions inner =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases found : resolve term outer (sameTerm operations term []) additions with
      | none =>
          have rawFound := found
          unfold resolve at rawFound
          simpa only [rawFound] using absence positive
      | some scope =>
          have rawFound := found
          unfold resolve at rawFound
          simp only [rawFound]
          split
          · trivial
          · exact worker_supports model sortDomain solver term outer sound (scope :: scopes) positive inner
  | not inner =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      exact worker_supports model sortDomain solver term outer sound scopes (!positive) inner
  | and parts | or parts =>
      simp only [SourceCompleteLogical.evaluate, SourceSubstitutionPrecedence.evaluateWith,
        SourceEnclosingRenames.evaluateWith, Logical]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals first | apply conjunction | apply disjunction
      all_goals
        intro part member
        exact worker_supports model sortDomain solver term outer sound scopes _ part
termination_by sizeOf inner

/-- Complete public evaluation derives both truth and falsity without solver completeness. -/
theorem public_supports (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (sound : ∀ guard, SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (positive : Bool) (guard : Guard Formula) :
    Guards.Supports (SourceSubstitutionPrecedence.evaluate operations solver (observe term) (sameTerm operations term) positive guard)
      (Public model sortDomain term positive guard) := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [SourceSubstitutionPrecedence.evaluate, Public]
      exact worker_supports model sortDomain solver term _ (sound _) [] positive _
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [SourceSubstitutionPrecedence.evaluate, Public]
          exact public_supports model sortDomain solver term sound positive inner
      | cons first rest =>
          simp only [SourceSubstitutionPrecedence.evaluate, Public]
          exact worker_supports model sortDomain solver term _ (sound _) [] positive _
  | not inner =>
      simp only [SourceSubstitutionPrecedence.evaluate, Public]
      exact public_supports model sortDomain solver term sound (!positive) inner
  | and parts | or parts =>
      simp only [SourceSubstitutionPrecedence.evaluate, Public]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals first | apply conjunction | apply disjunction
      all_goals
        intro part member
        exact public_supports model sortDomain solver term sound _ part
termination_by sizeOf guard

/-- In the unrestricted carrier, the source callback soundness supplies every complete guard domain. -/
theorem unrestricted_supports (model : Interpretation Value) (solver : SourceGuards.Entailment Formula)
    (sound : SourceEntailment.Sound model (fun _ _ => True) solver)
    (guard : Guard Formula) (term : Language.Term (Label Formula)) :
    Guards.Supports (SourceSubstitutionPrecedence.evaluateGuard operations solver guard term)
      (Public model (fun _ _ => True) term true guard) := by
  apply public_supports model (fun _ _ => True) solver term _ true guard
  intro context declarations antecedent consequent
  have evidence := sound declarations antecedent consequent
  simpa [SourceEntailment.Entails, SolverDomain, AmbientDomain] using evidence

end MicroCFTA.SourceSizedLiquidLogical
