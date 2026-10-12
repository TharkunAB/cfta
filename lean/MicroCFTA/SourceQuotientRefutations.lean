import MicroCFTA.SourceQuotientGuards
import MicroCFTA.SourceKnownHoldsTransport

/-!
# Logical refutation of current sparse guard No

The source can certify No only when its relevant query refutes the complete
logical judgment. Both polarities follow the source rules. Holds refutations
use the reverse known-actual map, including positional declarations.
-/
namespace MicroCFTA.SourceQuotientRefutations
open FullSyntax SourceFormula FormulaSubstitution SourceObservations
open SourceQuotientEnvironment SourceQuotientQueries SourceQuotientGuards
open SourceGuards (Guard Path Resolved)

private theorem observed_names (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (path : Path) (value : SourceGuards.Observed Formula) (requested : path ∈ SourceGuards.paths guard)
    (found : observe term path = some value) :
    ∀ name ∈ formulaNames value.refinement, name ∈ SourceGuards.usedNames operations (observe term) guard := by
  intro name member
  exact SourceSemanticNames.ambient_used operations (observe term) guard name
    (SourceScopeStack.observed_formula_names guard (observe term) path value requested found name member)

private theorem requirement_names (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (requirement : Formula) (member : requirement ∈ SourceGuards.requirements guard) (positive : Bool) :
    ∀ name ∈ formulaNames (if positive then requirement else operations.negate requirement),
      name ∈ SourceGuards.usedNames operations (observe term) guard := by
  intro name present
  apply SourceSemanticNames.ambient_used operations (observe term) guard
  apply SourceScopeStack.requirement_formula_names guard (observe term) requirement member
  cases positive <;> simpa only [Bool.false_eq_true, ↓reduceIte, operations, formulaNames] using present

/-- Every No from the repaired worker refutes complete logical satisfaction. -/
theorem worker_no (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term outer) solver)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term outer (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term outer (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (positive : Bool) (inner : Guard Formula) (included : Included outer inner)
    (no : evaluate solver term outer old positive inner = .no) :
    ¬Logical model sortDomain term outer new positive inner := by
  intro logical
  cases inner with
  | top | bottom => cases positive <;> simp_all [evaluate, SourceSubstitutionPrecedence.evaluateWith,
      SourceEnclosingRenames.evaluateWith, SourceGuards.polarize, Guards.negate, Logical]
  | same left right =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at no
      simp only [Logical] at logical
      cases leftFound : observe term left with
      | none => cases positive <;> simp_all [SourceGuards.absent]
      | some a => cases rightFound : observe term right with
        | none => cases positive <;> simp_all [SourceGuards.absent]
        | some b =>
            simp only [leftFound, rightFound] at no logical
            by_cases equal : left = right
            · subst right
              have polarity : positive = false := by cases positive <;> simp_all [SourceGuards.polarize, Guards.negate]
              subst positive
              obtain ⟨subterm, present, _⟩ := Option.map_eq_some_iff.mp leftFound
              have reflexive := (Language.termEq_correct (renameTree operations new subterm) _).mpr rfl
              simp [sameTerm, present, reflexive] at logical
            · simp only [equal, ↓reduceIte] at no
              cases decided : sameShape operations (observe term) old left right with
              | none => cases positive <;> simp_all [SourceGuards.polarize, Guards.negate]
              | some answer =>
                  have different : answer ≠ positive := by cases positive <;> cases answer <;>
                    simp_all [SourceGuards.polarize, Guards.negate]
                  have complete := same_sound model term outer recipes old new oldFound newFound left right answer decided
                  exact different (Option.some.inj (complete.symm.trans logical))
  | entails left right =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at no
      simp only [Logical] at logical
      cases leftFound : observe term left with
      | none => cases positive <;> simp_all [SourceGuards.absent]
      | some a => cases rightFound : observe term right with
        | none => cases positive <;> simp_all [SourceGuards.absent]
        | some b =>
            simp only [leftFound, rightFound] at no logical
            have leftNames := observed_names term outer left a (included.paths left (by simp [SourceGuards.paths])) leftFound
            have rightNames := observed_names term outer right b (included.paths right (by simp [SourceGuards.paths])) rightFound
            cases positive with
            | true =>
                exact SourceKnownQueryTransport.solver_no_logical model nullary laws sortDomain term outer solver sound recipes old new
                  oldFound newFound a.refinement b.refinement leftNames rightNames no logical
            | false =>
                have yes : SourceGuards.decideWith solver [] old
                    (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old a.refinement))
                    (SourceGuards.applySubstitutions operations old b.refinement) = .yes := by
                  cases result : SourceGuards.decideWith solver [] old _ _ <;> simp_all [SourceGuards.polarize, Guards.negate]
                exact logical (solver_yes_logical model nullary laws sortDomain term outer solver sound recipes old new oldFound newFound
                  accepted a.refinement b.refinement leftNames rightNames yes)
  | satisfies target requirement =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at no
      simp only [Logical] at logical
      cases found : observe term target with
      | none => cases positive <;> simp_all [SourceGuards.absent]
      | some value =>
          simp only [found] at no logical
          exact SourceKnownQueryTransport.solver_no_logical model nullary laws sortDomain term outer solver sound recipes old new
            oldFound newFound value.refinement _
            (observed_names term outer target value (included.paths target (by simp [SourceGuards.paths])) found)
            (requirement_names term outer requirement (included.requirements requirement (by simp [SourceGuards.requirements])) positive) no logical
  | holds targets requirement =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at no
      simp only [Logical] at logical
      cases found : SourceGuards.observeMany (observe term) targets with
      | none => cases positive <;> simp_all [SourceGuards.absent]
      | some values =>
          simp only [found] at no logical
          have bindings : (SourceGuards.contract operations targets values).1.map (fun name => (name, SourceGuards.valueName)) =
              (List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName)) := by
            simp [SourceGuards.contract, List.map_map, Function.comp_def]
          rw [bindings] at no
          exact SourceKnownHoldsTransport.solver_no_logical model nullary laws sortDomain term outer solver sound recipes old new
            oldFound newFound targets (by simpa only [SourceGuards.paths] using included.paths) values found _
            (requirement_names term outer requirement (included.requirements requirement (by simp [SourceGuards.requirements])) positive) no logical
  | substitute additions inner =>
      have requested : Requested outer additions := by
        intro entry member
        exact ⟨included.actuals entry.actual (by simp only [SourceGuards.actualPaths, List.mem_append, List.mem_map]; exact Or.inl ⟨entry, member, rfl⟩),
          included.paths entry.formal (by simp only [SourceGuards.paths, List.mem_append, List.mem_flatMap]; exact Or.inl ⟨entry, member, by simp⟩)⟩
      have inside : Included outer inner := ⟨fun path member => included.paths path (by simp [SourceGuards.paths, member]),
        fun path member => included.actuals path (by simp [SourceGuards.actualPaths, member]),
        (by simpa only [SourceGuards.requirements] using included.requirements)⟩
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at no
      simp only [Logical] at logical
      cases found : resolve term outer (sameShape operations (observe term) []) additions with
      | none =>
          have missing : resolve term outer (sameTerm operations term []) additions = none := by
            cases other : resolve term outer (sameTerm operations term []) additions with
            | none => rfl
            | some scope =>
                obtain ⟨oldScope, impossible⟩ := resolve_exists term outer _ (sameShape operations (observe term) []) additions scope other
                simp [found] at impossible
          have rawFound := found
          unfold resolve at rawFound
          cases positive <;> simp_all [SourceGuards.absent]
      | some scope =>
          obtain ⟨other, otherFound⟩ := resolve_exists term outer _ (sameTerm operations term []) additions scope found
          have rawFound := found
          unfold resolve at rawFound
          simp only [rawFound] at no
          cases passed : scope.any (SourceEnclosingRenames.renamedByEnclosing old) ||
              SourceSubstitutionPrecedence.ambiguousIdentityPrecedence scope with
          | true => simp [passed] at no
          | false =>
              simp only [passed, Bool.false_eq_true, ↓reduceIte] at no
              simp only [otherFound] at logical
              exact worker_no model nullary laws sortDomain solver term outer sound (additions :: recipes) (scope :: old) (other :: new)
                (.cons ⟨found, requested⟩ oldFound) (.cons ⟨otherFound, requested⟩ newFound)
                (accepted_cons scope old accepted passed) positive inner inside no logical
  | not inner =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at no
      simp only [Logical] at logical
      have inside : Included outer inner := by
        rcases included with ⟨paths, actuals, requirements⟩
        exact ⟨by simpa only [SourceGuards.paths] using paths, by simpa only [SourceGuards.actualPaths] using actuals,
          by simpa only [SourceGuards.requirements] using requirements⟩
      exact worker_no model nullary laws sortDomain solver term outer sound recipes old new oldFound newFound accepted (!positive)
        inner inside no logical
  | and parts | or parts =>
      have inside (part : Guard Formula) (member : part ∈ parts) : Included outer part :=
        ⟨fun path present => included.paths path (by simpa only [SourceGuards.paths] using List.mem_flatMap.mpr ⟨part, member, present⟩),
          fun path present => included.actuals path (by simpa only [SourceGuards.actualPaths] using List.mem_flatMap.mpr ⟨part, member, present⟩),
          fun formula present => included.requirements formula (by simpa only [SourceGuards.requirements] using List.mem_flatMap.mpr ⟨part, member, present⟩)⟩
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at no
      change SourceGuards.combine _ (parts.map (evaluate solver term outer old positive)) = .no at no
      simp only [Logical] at logical
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
      all_goals first
        | (obtain ⟨part, member, refuted⟩ := List.mem_map.mp ((GuardConjunction.combine_no _).mp no)
           exact worker_no model nullary laws sortDomain solver term outer sound recipes old new oldFound newFound accepted _ part
             (inside part member) refuted (logical part member))
        | (obtain ⟨⟨part, member⟩, proved⟩ := logical
           exact worker_no model nullary laws sortDomain solver term outer sound recipes old new oldFound newFound accepted _ part
             (inside part member) ((GuardConjunction.disjoin_no _).mp no _ (List.mem_map.mpr ⟨part, member, rfl⟩)) proved)
termination_by sizeOf inner

/-- A public sparse No excludes the full complete logical guard judgment. -/
theorem public_no (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (sound : ∀ guard, SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (positive : Bool) (guard : Guard Formula)
    (no : SourceSubstitutionPrecedence.evaluate operations solver (observe term) (sameShape operations (observe term)) positive guard = .no) :
    ¬Public model sortDomain term positive guard := by
  intro logical
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [SourceSubstitutionPrecedence.evaluate] at no
      simp only [Public] at logical
      exact worker_no model nullary laws sortDomain solver term _ (sound _) [] [] [] .nil .nil (by trivial) positive _
        ⟨fun _ member => member, fun _ member => member, fun _ member => member⟩ no logical
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [SourceSubstitutionPrecedence.evaluate] at no
          simp only [Public] at logical
          exact public_no model nullary laws sortDomain solver term sound positive inner no logical
      | cons first rest =>
          simp only [SourceSubstitutionPrecedence.evaluate] at no
          simp only [Public] at logical
          exact worker_no model nullary laws sortDomain solver term _ (sound _) [] [] [] .nil .nil (by trivial) positive _
            ⟨fun _ member => member, fun _ member => member, fun _ member => member⟩ no logical
  | not inner =>
      simp only [SourceSubstitutionPrecedence.evaluate] at no
      simp only [Public] at logical
      exact public_no model nullary laws sortDomain solver term sound (!positive) inner no logical
  | and parts | or parts =>
      simp only [SourceSubstitutionPrecedence.evaluate] at no
      simp only [Public] at logical
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
      all_goals first
        | (obtain ⟨part, member, refuted⟩ := List.mem_map.mp ((GuardConjunction.combine_no _).mp no)
           exact public_no model nullary laws sortDomain solver term sound _ part refuted (logical part member))
        | (obtain ⟨⟨part, member⟩, proved⟩ := logical
           exact public_no model nullary laws sortDomain solver term sound _ part
             ((GuardConjunction.disjoin_no _).mp no _ (List.mem_map.mpr ⟨part, member, rfl⟩)) proved)
termination_by sizeOf guard

/-- Both decided public verdicts support the complete logical judgment. -/
theorem public_supports (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (sound : ∀ guard, SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (positive : Bool) (guard : Guard Formula) :
    Guards.Supports (SourceSubstitutionPrecedence.evaluate operations solver (observe term)
      (sameShape operations (observe term)) positive guard) (Public model sortDomain term positive guard) := by
  cases result : SourceSubstitutionPrecedence.evaluate operations solver (observe term)
      (sameShape operations (observe term)) positive guard with
  | unknown => trivial
  | yes => exact public_yes model nullary laws sortDomain solver term sound positive guard result
  | no => exact public_no model nullary laws sortDomain solver term sound positive guard result

/-- A decided sparse public verdict equals complete logical validity. -/
theorem decided_iff (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (sound : ∀ guard, SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (positive : Bool) (guard : Guard Formula)
    (decided : SourceSubstitutionPrecedence.evaluate operations solver (observe term)
      (sameShape operations (observe term)) positive guard ≠ .unknown) :
    SourceSubstitutionPrecedence.evaluate operations solver (observe term)
      (sameShape operations (observe term)) positive guard = .yes ↔ Public model sortDomain term positive guard := by
  have support := public_supports model nullary laws sortDomain solver term sound positive guard
  cases result : SourceSubstitutionPrecedence.evaluate operations solver (observe term)
      (sameShape operations (observe term)) positive guard <;> simp_all [Guards.Supports]

end MicroCFTA.SourceQuotientRefutations
