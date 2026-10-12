import MicroCFTA.SourceKnownQueryTransport
import MicroCFTA.SourceQuotientHolds
import MicroCFTA.GuardConjunction

/-!
# Logical guard soundness through actual identification

The logical judgment follows the source polarity rules. Negative Entails
refutes entailment. Negative Satisfies and Holds entail the negated formula.
The theorem permits ambiguous actuals when the executed scope checks pass.
-/
namespace MicroCFTA.SourceQuotientGuards
open FullSyntax SourceFormula FormulaSubstitution SourceObservations
open SourceQuotientEnvironment SourceQuotientQueries
open SourceGuards (Guard Path Resolved)

/-- A nested guard uses only the outer table's requested positions and formulas. -/
structure Included (outer inner : Guard Formula) : Prop where
  paths : ∀ path ∈ SourceGuards.paths inner, path ∈ SourceGuards.paths outer
  actuals : ∀ path ∈ SourceGuards.actualPaths inner, path ∈ SourceGuards.actualPaths outer
  requirements : ∀ formula ∈ SourceGuards.requirements inner, formula ∈ SourceGuards.requirements outer

/-- Execute the current source worker with its single outer allocation table. -/
def evaluate (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (outer : Guard Formula) (scopes : List Scope) (positive : Bool) (inner : Guard Formula) : Guards.Verdict :=
  let table := SourceGuards.substitutionValues operations (observe term) (sameShape operations (observe term) []) outer
  SourceSubstitutionPrecedence.evaluateWith operations solver (observe term) (sameShape operations (observe term))
    table.1 table.2 scopes positive inner

/-- The complete mathematical query includes the source actual assumptions and declarations. -/
def Query (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (outer : Guard Formula) (scopes : List Scope)
    (antecedent consequent : Formula) : Prop :=
  SourceEntailment.Entails model (Domain sortDomain term outer scopes)
    (SourceGuards.withActualAssumptions operations scopes (SourceGuards.applySubstitutions operations scopes antecedent))
    (SourceGuards.applySubstitutions operations scopes consequent)

/-- Complete logical satisfaction follows each source constructor and its polarity. -/
def Logical (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (outer : Guard Formula) (scopes : List Scope)
    (positive : Bool) (inner : Guard Formula) : Prop :=
  match inner with
  | .top => positive = true
  | .bottom => positive = false
  | .same left right =>
      match observe term left, observe term right with
      | some _, some _ => sameTerm operations term scopes left right = some positive
      | _, _ => positive = false
  | .entails left right =>
      match observe term left, observe term right with
      | some a, some b => if positive then Query model sortDomain term outer scopes a.refinement b.refinement
          else ¬Query model sortDomain term outer scopes a.refinement b.refinement
      | _, _ => positive = false
  | .satisfies target requirement =>
      match observe term target with
      | some value => Query model sortDomain term outer scopes value.refinement
          (if positive then requirement else operations.negate requirement)
      | none => positive = false
  | .holds targets requirement =>
      match SourceGuards.observeMany (observe term) targets with
      | some values => SourceEntailment.Entails model (SourceQuotientHolds.Domain sortDomain term outer targets.length scopes)
          (SourceGuards.withActualAssumptions operations scopes
            (SourceGuards.applySubstitutions operations scopes (SourceGuards.contract operations targets values).2))
          (SourceGuards.applySubstitutions operations scopes (if positive then requirement else operations.negate requirement))
      | none => positive = false
  | .substitute additions inner =>
      match resolve term outer (sameTerm operations term []) additions with
      | some resolved => Logical model sortDomain term outer (resolved :: scopes) positive inner
      | none => positive = false
  | .not inner => Logical model sortDomain term outer scopes (!positive) inner
  | .and parts => if positive then ∀ part ∈ parts, Logical model sortDomain term outer scopes positive part
      else ∃ part : {guard // guard ∈ parts}, Logical model sortDomain term outer scopes positive part.val
  | .or parts => if positive then ∃ part : {guard // guard ∈ parts}, Logical model sortDomain term outer scopes positive part.val
      else ∀ part ∈ parts, Logical model sortDomain term outer scopes positive part
termination_by sizeOf inner
decreasing_by
  all_goals first | decreasing_tactic | (have bound := List.sizeOf_lt_of_mem part.property; simp_all only [SourceGuards.Guard.and.sizeOf_spec, SourceGuards.Guard.or.sizeOf_spec]; omega)

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

/-- Actual identity allocation does not alter literal structural substitutions. -/
theorem roots (ambient : List Name) (old new : List Scope)
    (paired : Language.All₂ (Language.All₂ (Pair ambient)) old new) (label : Label Formula) :
    renameRoot operations old label = renameRoot operations new label := by
  induction paired generalizing label with
  | nil => rfl
  | @cons first second rest other head tail ih =>
      have entries : first.map Resolved.symbolReplacement = second.map Resolved.symbolReplacement := by
        induction head with
        | nil => rfl
        | cons row rows ih => simp [row.symbols, ih]
      have symbols : symbolEntries first = symbolEntries second := by simp only [symbolEntries, entries]
      have maps : symbolMap first = symbolMap second := by simp only [symbolMap, symbols]
      simp only [renameRoot, List.foldl_cons, symbols, maps]
      exact ih _

/-- A decided sparse structural comparison survives complete identity allocation. -/
theorem same_sound (model : Interpretation Value) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term guard (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term guard (sameTerm operations term []) recipes new)
    (left right : Path) (answer : Bool)
    (decided : sameShape operations (observe term) old left right = some answer) :
    sameTerm operations term new left right = some answer := by
  have paired := (stack_pair model term guard recipes old new oldFound newFound (fun _ => model.literal 0)).1
  have equal : sameShape operations (observe term) old left right = sameShape operations (observe term) new left right := by
    simp only [sameShape, renameObserved, roots _ old new paired]
  rw [equal] at decided
  exact sameShape_sound operations term new left right answer decided

private theorem same_self (term : Language.Term (Label Formula)) (scopes : List Scope)
    (path : Path) (value : SourceGuards.Observed Formula) (found : observe term path = some value) :
    sameTerm operations term scopes path path = some true := by
  obtain ⟨subterm, present, _⟩ := Option.map_eq_some_iff.mp found
  simp only [sameTerm, present, pure]
  exact congrArg some ((Language.termEq_correct _ _).mpr rfl)

private theorem absence (positive : Bool) (yes : SourceGuards.absent positive = .yes) : positive = false := by
  cases positive <;> simp_all [SourceGuards.absent]

/-- Every Yes from the current worker proves the complete logical guard judgment. -/
theorem worker_yes (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula)) (outer : Guard Formula)
    (sound : SourceEntailment.Sound model (SolverDomain sortDomain term outer) solver)
    (recipes : List Recipe) (old new : List Scope)
    (oldFound : Resolves term outer (sameShape operations (observe term) []) recipes old)
    (newFound : Resolves term outer (sameTerm operations term []) recipes new)
    (accepted : Accepted old) (positive : Bool) (inner : Guard Formula) (included : Included outer inner)
    (yes : evaluate solver term outer old positive inner = .yes) :
    Logical model sortDomain term outer new positive inner := by
  cases inner with
  | top | bottom => cases positive <;> simp_all [evaluate, SourceSubstitutionPrecedence.evaluateWith,
      SourceEnclosingRenames.evaluateWith, SourceGuards.polarize, Guards.negate, Logical]
  | same left right =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      cases leftFound : observe term left with
      | none => simpa only [leftFound] using absence positive (by simpa only [leftFound] using yes)
      | some a => cases rightFound : observe term right with
        | none => simpa only [leftFound, rightFound] using absence positive (by simpa only [leftFound, rightFound] using yes)
        | some b =>
            simp only [leftFound, rightFound] at yes ⊢
            by_cases equal : left = right
            · subst right
              have polarity : positive = true := by cases positive <;> simp_all [SourceGuards.polarize, Guards.negate]
              subst positive
              exact same_self term new left a leftFound
            · simp only [equal, ↓reduceIte] at yes
              cases decided : sameShape operations (observe term) old left right with
              | none => cases positive <;> simp_all [SourceGuards.polarize, Guards.negate]
              | some answer =>
                  have polarity : answer = positive := by cases positive <;> cases answer <;>
                    simp_all [SourceGuards.polarize, Guards.negate]
                  subst answer
                  exact same_sound model term outer recipes old new oldFound newFound left right positive decided
  | entails left right =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      cases leftFound : observe term left with
      | none => simpa only [leftFound] using absence positive (by simpa only [leftFound] using yes)
      | some a => cases rightFound : observe term right with
        | none => simpa only [leftFound, rightFound] using absence positive (by simpa only [leftFound, rightFound] using yes)
        | some b =>
            simp only [leftFound, rightFound] at yes ⊢
            have leftNames := observed_names term outer left a (included.paths left (by simp [SourceGuards.paths])) leftFound
            have rightNames := observed_names term outer right b (included.paths right (by simp [SourceGuards.paths])) rightFound
            cases positive with
            | true =>
                exact solver_yes_logical model nullary laws sortDomain term outer solver sound recipes old new oldFound newFound
                  accepted a.refinement b.refinement leftNames rightNames yes
            | false =>
                have no : SourceGuards.decideWith solver [] old
                    (SourceGuards.withActualAssumptions operations old (SourceGuards.applySubstitutions operations old a.refinement))
                    (SourceGuards.applySubstitutions operations old b.refinement) = .no := by
                  cases result : SourceGuards.decideWith solver [] old _ _ <;> simp_all [SourceGuards.polarize, Guards.negate]
                exact SourceKnownQueryTransport.solver_no_logical model nullary laws sortDomain term outer solver sound recipes old new
                  oldFound newFound a.refinement b.refinement leftNames rightNames no
  | satisfies target requirement =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      cases found : observe term target with
      | none => simpa only [found] using absence positive (by simpa only [found] using yes)
      | some value =>
          simp only [found] at yes ⊢
          exact solver_yes_logical model nullary laws sortDomain term outer solver sound recipes old new oldFound newFound accepted
            value.refinement _ (observed_names term outer target value (included.paths target (by simp [SourceGuards.paths])) found)
            (requirement_names term outer requirement (included.requirements requirement (by simp [SourceGuards.requirements])) positive) yes
  | holds targets requirement =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      cases found : SourceGuards.observeMany (observe term) targets with
      | none => simpa only [found] using absence positive (by simpa only [found] using yes)
      | some values =>
          simp only [found] at yes ⊢
          have bindings : (SourceGuards.contract operations targets values).1.map (fun name => (name, SourceGuards.valueName)) =
              (List.range targets.length).map (fun index => (SourceGuards.contractName index, SourceGuards.valueName)) := by
            simp [SourceGuards.contract, List.map_map, Function.comp_def]
          rw [bindings] at yes
          exact SourceQuotientHolds.solver_yes_logical model nullary laws sortDomain term outer solver sound recipes old new
            oldFound newFound accepted targets (by simpa only [SourceGuards.paths] using included.paths) values found _
            (requirement_names term outer requirement (included.requirements requirement (by simp [SourceGuards.requirements])) positive) yes
  | substitute additions inner =>
      have requested : Requested outer additions := by
        intro entry member
        exact ⟨included.actuals entry.actual (by simp only [SourceGuards.actualPaths, List.mem_append, List.mem_map]; exact Or.inl ⟨entry, member, rfl⟩),
          included.paths entry.formal (by simp only [SourceGuards.paths, List.mem_append, List.mem_flatMap]; exact Or.inl ⟨entry, member, by simp⟩)⟩
      have inside : Included outer inner := ⟨fun path member => included.paths path (by simp [SourceGuards.paths, member]),
        fun path member => included.actuals path (by simp [SourceGuards.actualPaths, member]), (by simpa only [SourceGuards.requirements] using included.requirements)⟩
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
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
          simpa only [missing] using absence positive (by simpa only [rawFound] using yes)
      | some scope =>
          obtain ⟨other, otherFound⟩ := resolve_exists term outer _ (sameTerm operations term []) additions scope found
          have rawFound := found
          unfold resolve at rawFound
          simp only [rawFound] at yes
          cases passed : scope.any (SourceEnclosingRenames.renamedByEnclosing old) ||
              SourceSubstitutionPrecedence.ambiguousIdentityPrecedence scope with
          | true => simp [passed] at yes
          | false =>
              simp only [passed, Bool.false_eq_true, ↓reduceIte] at yes
              simp only [otherFound]
              exact worker_yes model nullary laws sortDomain solver term outer sound (additions :: recipes) (scope :: old) (other :: new)
                (.cons ⟨found, requested⟩ oldFound) (.cons ⟨otherFound, requested⟩ newFound)
                (accepted_cons scope old accepted passed) positive inner inside yes
  | not inner =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      simp only [Logical]
      have inside : Included outer inner := by
        rcases included with ⟨paths, actuals, requirements⟩
        exact ⟨by simpa only [SourceGuards.paths] using paths, by simpa only [SourceGuards.actualPaths] using actuals,
          by simpa only [SourceGuards.requirements] using requirements⟩
      exact worker_yes model nullary laws sortDomain solver term outer sound recipes old new oldFound newFound accepted (!positive)
        inner inside yes
  | and parts | or parts =>
      have inside (part : Guard Formula) (member : part ∈ parts) : Included outer part :=
        ⟨fun path present => included.paths path (by simpa only [SourceGuards.paths] using List.mem_flatMap.mpr ⟨part, member, present⟩),
          fun path present => included.actuals path (by simpa only [SourceGuards.actualPaths] using List.mem_flatMap.mpr ⟨part, member, present⟩),
          fun formula present => included.requirements formula (by simpa only [SourceGuards.requirements] using List.mem_flatMap.mpr ⟨part, member, present⟩)⟩
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] at yes
      change SourceGuards.combine _ (parts.map (evaluate solver term outer old positive)) = .yes at yes
      simp only [Logical]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
      all_goals first
        | (intro part member
           apply worker_yes model nullary laws sortDomain solver term outer sound recipes old new oldFound newFound accepted _ part (inside part member)
           exact (GuardConjunction.combine_yes _).mp yes _ (List.mem_map.mpr ⟨part, member, rfl⟩))
        | (obtain ⟨part, member, proved⟩ := List.mem_map.mp ((GuardConjunction.disjoin_yes _).mp yes)
           exact ⟨⟨part, member⟩, worker_yes model nullary laws sortDomain solver term outer sound recipes old new oldFound newFound accepted _
             part (inside part member) proved⟩)
termination_by sizeOf inner

/-- Public Boolean operands have their own source actual-allocation context. -/
def Public (model : Interpretation Value) (sortDomain : Name → Value → Prop)
    (term : Language.Term (Label Formula)) (positive : Bool) (guard : Guard Formula) : Prop :=
  match guard with
  | .and parts => if positive then ∀ part ∈ parts, Public model sortDomain term positive part
      else ∃ part : {guard // guard ∈ parts}, Public model sortDomain term positive part.val
  | .or parts => if positive then ∃ part : {guard // guard ∈ parts}, Public model sortDomain term positive part.val
      else ∀ part ∈ parts, Public model sortDomain term positive part
  | .not inner => Public model sortDomain term (!positive) inner
  | .substitute [] inner => Public model sortDomain term positive inner
  | guard => Logical model sortDomain term guard [] positive guard
termination_by sizeOf guard
decreasing_by
  all_goals first | decreasing_tactic | (have bound := List.sizeOf_lt_of_mem part.property; simp_all only [SourceGuards.Guard.and.sizeOf_spec, SourceGuards.Guard.or.sizeOf_spec]; omega)

/-- The public evaluator's Yes is logically valid without exact complete-backend verdict stability. -/
theorem public_yes (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (Label Formula))
    (sound : ∀ guard, SourceEntailment.Sound model (SolverDomain sortDomain term guard) solver)
    (positive : Bool) (guard : Guard Formula)
    (yes : SourceSubstitutionPrecedence.evaluate operations solver (observe term) (sameShape operations (observe term)) positive guard = .yes) :
    Public model sortDomain term positive guard := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [SourceSubstitutionPrecedence.evaluate] at yes
      simp only [Public]
      exact worker_yes model nullary laws sortDomain solver term _ (sound _) [] [] [] .nil .nil (by trivial) positive _
        ⟨fun _ member => member, fun _ member => member, fun _ member => member⟩ yes
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [SourceSubstitutionPrecedence.evaluate] at yes
          simp only [Public]
          exact public_yes model nullary laws sortDomain solver term sound positive inner yes
      | cons first rest =>
          simp only [SourceSubstitutionPrecedence.evaluate] at yes
          simp only [Public]
          exact worker_yes model nullary laws sortDomain solver term _ (sound _) [] [] [] .nil .nil (by trivial) positive _
            ⟨fun _ member => member, fun _ member => member, fun _ member => member⟩ yes
  | not inner =>
      simp only [SourceSubstitutionPrecedence.evaluate] at yes
      simp only [Public]
      exact public_yes model nullary laws sortDomain solver term sound (!positive) inner yes
  | and parts | or parts =>
      simp only [SourceSubstitutionPrecedence.evaluate] at yes
      simp only [Public]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
      all_goals first
        | (intro part member
           apply public_yes model nullary laws sortDomain solver term sound _ part
           exact (GuardConjunction.combine_yes _).mp yes _ (List.mem_map.mpr ⟨part, member, rfl⟩))
        | (obtain ⟨part, member, proved⟩ := List.mem_map.mp ((GuardConjunction.disjoin_yes _).mp yes)
           exact ⟨⟨part, member⟩, public_yes model nullary laws sortDomain solver term sound _ part proved⟩)
termination_by sizeOf guard

end MicroCFTA.SourceQuotientGuards
