import MicroCFTA.ParentIntegerSettlement
import MicroCFTA.DefiningTerm

/-!
# Integer parent guard substitution

Supported parent guards substitute exact target measures simultaneously.
The mathematical interpretation does not identify solver verdicts with truth.
-/
namespace MicroCFTA.ParentGuardFormula
open FullSyntax FormulaSubstitution
open SourceGuards (contractName valueName)

/-- A missing replacement name has no lookup result. -/
theorem lookup_absent (active : List (Name × Term)) (name : Name)
    (absent : name ∉ active.map Prod.fst) : lookup name active = none := by
  induction active with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, term⟩
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp [lookup, absent.1, ih absent.2]

/-- The source identity test accepts exactly the variable with the same name. -/
theorem identity_exact (entry : Name × Term) :
    identityReplacement entry = true ↔ entry.2 = .var entry.1 := by
  rcases entry with ⟨name, term⟩
  cases term <;> simp [identityReplacement]
  rename_i other
  exact eq_comm

/-- With distinct formal names, deleting identity substitutions preserves the simultaneous value environment. -/
theorem assignment_filter_identity (env : Name → Int) (active : List (Name × Term))
    (distinct : (active.map Prod.fst).Nodup) :
    assignment integerModel env (active.filter fun entry => !identityReplacement entry) =
      assignment integerModel env active := by
  induction active with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, term⟩
      have unique := List.nodup_cons.mp distinct
      have tail := ih unique.2
      by_cases identity : identityReplacement (key, term) = true
      · have same : term = .var key := (identity_exact _).mp identity
        subst term
        simp only [List.filter_cons, identity, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [tail]
        funext name
        by_cases equal : name = key
        · subst name
          simp [assignment, lookup, lookup_absent rest key unique.1, evaluateTerm]
        · simp [assignment, lookup, equal]
      · have kept : identityReplacement (key, term) = false := by simpa using identity
        simp only [List.filter_cons, kept, Bool.not_false, ↓reduceIte]
        funext name
        by_cases equal : name = key
        · simp [assignment, lookup, equal]
        · have same := congrFun tail name
          simpa [assignment, lookup, equal] using same

/-- Mathematical assignment of actual integer values to positional formals uses the first occurrence. -/
def namedEnvironment (env : Name → Int) : List (Name × Int) → Name → Int
  | [], name => env name
  | (key, value) :: rest, name => if name = key then value else namedEnvironment env rest name

/-- Equal target values replace all positional names in one simultaneous environment. -/
theorem assignment_values (env : Name → Int) (names : List Name) (terms : List Term) (values : List Int)
    (exactValues : Language.All₂ (fun term value => evaluateTerm integerModel env term = value) terms values) :
    assignment integerModel env (names.zip terms) = namedEnvironment env (names.zip values) := by
  induction exactValues generalizing names with
  | nil => funext name; simp [assignment, lookup, namedEnvironment]
  | @cons term value terms values exactValue rest ih =>
      cases names with
      | nil => funext name; simp [assignment, lookup, namedEnvironment]
      | cons name names =>
          funext found
          by_cases same : found = name
          · simp [assignment, lookup, namedEnvironment, same, exactValue]
          · have tail := congrFun (ih names) found
            simpa [assignment, lookup, namedEnvironment, same] using tail

/-- Zipping replacement terms cannot introduce a repeated formal name. -/
theorem zip_names_distinct (names : List Name) (terms : List Term) (distinct : names.Nodup) :
    ((names.zip terms).map Prod.fst).Nodup := by
  induction names generalizing terms with
  | nil => simp
  | cons name names ih =>
      cases terms with
      | nil => simp
      | cons term terms =>
          simp only [List.zip_cons_cons, List.map_cons, List.nodup_cons]
          refine ⟨?_, ih terms (List.nodup_cons.mp distinct).2⟩
          intro member
          obtain ⟨entry, member, same⟩ := List.mem_map.mp member
          exact (List.nodup_cons.mp distinct).1 (same ▸ (List.of_mem_zip member).1)

/-- Checked source substitution has exactly the requirement's mathematical actual-value interpretation. -/
theorem substitution_values (env : Name → Int) (names : List Name) (terms : List Term) (values : List Int)
    (distinct : names.Nodup)
    (exactValues : Language.All₂ (fun term value => evaluateTerm integerModel env term = value) terms values)
    (input output : Formula) (built : checked (names.zip terms) input = .ok output) :
    Holds integerModel env output ↔ Holds integerModel (namedEnvironment env (names.zip values)) input := by
  rw [FormulaCorrectness.checked_semantics integerModel (by intro value; rfl) _ _ _ built env,
    assignment_filter_identity env _ (zip_names_distinct names terms distinct),
    assignment_values env names terms values exactValues]

/-- Source positional contract names have distinct decimal indices. -/
theorem contractName_injective : Function.Injective contractName := by
  intro left right same
  apply Nat.repr_injective
  exact String.append_right_inj "__cfta_contract_" |>.mp same

/-- Every target gets a different positional formal, even when target paths repeat. -/
theorem contractNames_distinct (count : Nat) : ((List.range count).map contractName).Nodup := by
  apply List.pairwise_map.mpr
  exact (List.nodup_range : (List.range count).Nodup).imp
    (fun different same => different (contractName_injective same))

/-- The parent reads its own refinement or one already-renamed immediate child root. -/
def targetRefinement (root : Formula) (children : List (Option Formula)) : SourceGuards.Path → Option Formula
  | [] => some root
  | [index] => (children[index]?).join
  | _ => none

/-- Source targetTerm uses the exact onlyPoint-first extractor after path lookup. -/
def targetTerm (root : Formula) (children : List (Option Formula)) (target : SourceGuards.Path) : Option Term :=
  (targetRefinement root children target).bind DefiningTerm.termOf

/-- The source renamedRoot table keeps missing observations and applies each actual coordinate offset. -/
def renamedRoots (keys : List OpenIntegerKeys.Key) (observed : OpenIntegerKeys.Key → Option Formula) :
    List (Option Formula) :=
  (OpenIntegerKeys.placed keys).map fun entry =>
    (observed entry.2).map (OpenIntegerKeys.renameFrom entry.1 entry.2.width)

/-- Immediate target lookup reads the same allocated child block and optional renamed root. -/
theorem renamed_child (root : Formula) (keys : List OpenIntegerKeys.Key)
    (observed : OpenIntegerKeys.Key → Option Formula) (index : Nat) :
    targetRefinement root (renamedRoots keys observed) [index] =
      ((OpenIntegerKeys.placed keys)[index]?).bind fun entry =>
        (observed entry.2).map (OpenIntegerKeys.renameFrom entry.1 entry.2.width) := by
  simp only [targetRefinement, renamedRoots, List.getElem?_map]
  cases (OpenIntegerKeys.placed keys)[index]? <;> rfl

/-- Actual child renaming gives the precise environment in which its refinement must hold. -/
theorem renamed_refinement (env : Name → Int) (offset width : Nat) (formula : Formula) (value : Int) :
    Holds integerModel (update env valueName value) (OpenIntegerKeys.renameFrom offset width formula) ↔
      Holds integerModel
        (SourceFormula.renamedEnvironment integerModel (update env valueName value)
          (OpenIntegerKeys.renamePairs offset width)) formula :=
  SourceFormula.substitute_semantics integerModel (by intro actual; rfl) _ _ _

/-- Holds visits every target in its supplied order and fails at the first absent measure. -/
def targetTerms (root : Formula) (children : List (Option Formula)) : List SourceGuards.Path → Option (List Term)
  | [] => some []
  | target :: rest => do
      let term ← targetTerm root children target
      let terms ← targetTerms root children rest
      some (term :: terms)

/-- Unsupported paths or guards retain the full guard; checked substitution failures stay distinct. -/
inductive TranslationError where
  | integerRead (part : SourceGuards.Guard Formula)
  | substitution (error : FormulaSubstitution.Error)

/-- Execute the complete source partFormula dispatch for open parent guards. -/
def partFormula (root : Formula) (children : List (Option Formula))
    (part : SourceGuards.Guard Formula) : Except TranslationError Formula :=
  match part with
  | .satisfies target requirement =>
      match targetTerm root children target with
      | none => .error (.integerRead part)
      | some term => (checked [(valueName, term)] requirement).mapError TranslationError.substitution
  | .holds targets requirement =>
      match targetTerms root children targets with
      | none => .error (.integerRead part)
      | some terms => (checked (((List.range targets.length).map contractName).zip terms) requirement).mapError TranslationError.substitution
  | _ => .error (.integerRead part)

/-- An unsupported deeper path cannot yield a measure, even if the root formula is exact. -/
theorem deeper_target (root : Formula) (children : List (Option Formula)) (first second : Nat) (rest : List Nat) :
    targetTerm root children (first :: second :: rest) = none := rfl

/-- A missing immediate root remains absent. -/
theorem missing_child (root : Formula) (children : List (Option Formula)) (index : Nat)
    (missing : (children[index]?).join = none) : targetTerm root children [index] = none := by
  simp [targetTerm, targetRefinement, missing]

/-- A missing measure at any requested target prevents a Holds translation. -/
theorem targetTerms_missing (root : Formula) (children : List (Option Formula))
    (targets : List SourceGuards.Path) (target : SourceGuards.Path) (member : target ∈ targets)
    (missing : targetTerm root children target = none) : targetTerms root children targets = none := by
  induction targets with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [targetTerms, missing, Bind.bind, Option.bind]
      · cases firstFound : targetTerm root children first <;>
          simp [targetTerms, firstFound, ih member, Bind.bind, Option.bind]

/-- Failed Holds lookup preserves the whole original guard as the source error payload. -/
theorem holds_missing (root : Formula) (children : List (Option Formula))
    (targets : List SourceGuards.Path) (requirement : Formula) (target : SourceGuards.Path)
    (member : target ∈ targets) (missing : targetTerm root children target = none) :
    partFormula root children (.holds targets requirement) = .error (.integerRead (.holds targets requirement)) := by
  simp [partFormula, targetTerms_missing root children targets target member missing]

/-- The checked substitution failure represents the source substitution exception separately from IntegerLeafRead. -/
theorem satisfies_substitution_error (root : Formula) (children : List (Option Formula))
    (target : SourceGuards.Path) (requirement : Formula) (term : Term)
    (found : targetTerm root children target = some term) (error : FormulaSubstitution.Error)
    (failed : checked [(valueName, term)] requirement = .error error) :
    partFormula root children (.satisfies target requirement) = .error (.substitution error) := by
  simp [partFormula, found, failed, Except.mapError]

/-- Successful target extraction derives value independence from the source caller check. -/
theorem target_independent (root : Formula) (children : List (Option Formula))
    (target : SourceGuards.Path) (term : Term) (found : targetTerm root children target = some term) :
    valueName ∉ termNames term := by
  cases observed : targetRefinement root children target with
  | none => simp [targetTerm, observed] at found
  | some refinement =>
      exact DefiningTerm.termOf_independent refinement term (by simpa [targetTerm, observed] using found)

/-- Successful target extraction defines exactly one value in every ambient environment. -/
theorem target_exact (env : Name → Int) (root : Formula) (children : List (Option Formula))
    (target : SourceGuards.Path) (term : Term) (refinement : Formula)
    (found : targetTerm root children target = some term)
    (observed : targetRefinement root children target = some refinement) (value : Int) :
    Holds integerModel (update env valueName value) refinement ↔
      value = evaluateTerm integerModel env term :=
  DefiningTerm.termOf_exact env refinement term (by simpa [targetTerm, observed] using found) value

/-- Read the extracted value; the default applies only when extraction fails. -/
noncomputable def extractedValue (env : Name → Int) (root : Formula) (children : List (Option Formula))
    (target : SourceGuards.Path) : Int :=
  ((targetTerm root children target).map (evaluateTerm integerModel env)).getD 0

/-- A successful translation has an extracted measure at every listed target. -/
theorem partFormula_target (root : Formula) (children : List (Option Formula))
    (part : SourceGuards.Guard Formula) (output : Formula)
    (built : partFormula root children part = .ok output)
    (target : SourceGuards.Path) (member : target ∈ SourceGuards.paths part) :
    ∃ term, targetTerm root children target = some term := by
  cases found : targetTerm root children target with
  | some term => exact ⟨term, rfl⟩
  | none =>
      cases part with
      | satisfies path requirement =>
          have same : target = path := by simpa [SourceGuards.paths] using member
          subst target
          simp [partFormula, found] at built
      | holds targets requirement =>
          have absent := targetTerms_missing root children targets target
            (by simpa [SourceGuards.paths] using member) found
          simp [partFormula, absent] at built
      | _ => simp [partFormula] at built

/-- Successful target extraction denotes its actual value from the observed refinement. -/
theorem target_value (env : Name → Int) (root : Formula) (children : List (Option Formula))
    (target : SourceGuards.Path) (term : Term) (value : Int)
    (found : targetTerm root children target = some term)
    (refined : ∀ refinement, targetRefinement root children target = some refinement →
      Holds integerModel (update env valueName value) refinement) : evaluateTerm integerModel env term = value := by
  cases observed : targetRefinement root children target with
  | none => simp [targetTerm, observed] at found
  | some refinement =>
      have extracted : DefiningTerm.termOf refinement = some term := by simpa [targetTerm, observed] using found
      exact DefiningTerm.termOf_base_exact env refinement term value extracted (refined refinement observed)

/-- Ordered target traversal preserves the corresponding actual-value order, including repeated paths. -/
theorem targets_values (env : Name → Int) (root : Formula) (children : List (Option Formula))
    (values : SourceGuards.Path → Int) (targets : List SourceGuards.Path) (terms : List Term)
    (found : targetTerms root children targets = some terms)
    (refined : ∀ target ∈ targets, ∀ refinement, targetRefinement root children target = some refinement →
      Holds integerModel (update env valueName (values target)) refinement) :
    Language.All₂ (fun term value => evaluateTerm integerModel env term = value) terms (targets.map values) := by
  induction targets generalizing terms with
  | nil => cases found; exact .nil
  | cons target rest ih =>
      cases head : targetTerm root children target with
      | none => simp [targetTerms, head, Bind.bind, Option.bind] at found
      | some term =>
          cases tail : targetTerms root children rest with
          | none => simp [targetTerms, head, tail, Bind.bind, Option.bind] at found
          | some remaining =>
              have same : terms = term :: remaining := by
                simpa [targetTerms, head, tail, Bind.bind, Option.bind] using found.symm
              subst terms
              exact .cons (target_value env root children target term (values target) head
                (refined target (by simp)))
                (ih remaining tail (fun target member => refined target (by simp [member])))

/-- Mathematical guard truth on the exact integer values of the selected roots. -/
def actualGuard (env : Name → Int) (values : SourceGuards.Path → Int) : SourceGuards.Guard Formula → Prop
  | .satisfies target requirement => Holds integerModel (update env valueName (values target)) requirement
  | .holds targets requirement => Holds integerModel
      (namedEnvironment env (((List.range targets.length).map contractName).zip (targets.map values))) requirement
  | _ => False

/-- A successful parent translation is equivalent to its guard on the actual exact target values. -/
theorem partFormula_exact (env : Name → Int) (root : Formula) (children : List (Option Formula))
    (values : SourceGuards.Path → Int) (part : SourceGuards.Guard Formula) (output : Formula)
    (built : partFormula root children part = .ok output)
    (refined : ∀ target ∈ SourceGuards.paths part, ∀ refinement,
      targetRefinement root children target = some refinement →
        Holds integerModel (update env valueName (values target)) refinement) :
    Holds integerModel env output ↔ actualGuard env values part := by
  cases part with
  | satisfies target requirement =>
      cases found : targetTerm root children target with
      | none => simp [partFormula, found] at built
      | some term =>
          have checked : FormulaSubstitution.checked [(valueName, term)] requirement = .ok output := by
            cases result : FormulaSubstitution.checked [(valueName, term)] requirement <;>
              simp [partFormula, found, result, Except.mapError] at built ⊢
            exact built
          have value := target_value env root children target term (values target) found
            (refined target (by simp [SourceGuards.paths]))
          have result := substitution_values env [valueName] [term] [values target] (by simp)
            (.cons value .nil) requirement output checked
          have same : namedEnvironment env [(valueName, values target)] = update env valueName (values target) := by
            funext name
            simp [namedEnvironment, update]
          simpa only [actualGuard, List.zip_cons_cons, List.zip_nil_left, same] using result
  | holds targets requirement =>
      cases found : targetTerms root children targets with
      | none => simp [partFormula, found] at built
      | some terms =>
          have checked : FormulaSubstitution.checked (((List.range targets.length).map contractName).zip terms)
              requirement = .ok output := by
            cases result : FormulaSubstitution.checked (((List.range targets.length).map contractName).zip terms)
                requirement <;> simp [partFormula, found, result, Except.mapError] at built ⊢
            exact built
          exact substitution_values env _ terms (targets.map values) (contractNames_distinct targets.length)
            (targets_values env root children values targets terms found
              (by simpa only [SourceGuards.paths] using refined)) requirement output checked
  | _ => simp [partFormula] at built

/-- The source caller gate derives exact guard meaning without a target satisfiability premise. -/
theorem partFormula_derived (env : Name → Int) (root : Formula) (children : List (Option Formula))
    (part : SourceGuards.Guard Formula) (output : Formula)
    (built : partFormula root children part = .ok output) :
    Holds integerModel env output ↔ actualGuard env (extractedValue env root children) part := by
  apply partFormula_exact env root children (extractedValue env root children) part output built
  intro target member refinement observed
  obtain ⟨term, found⟩ := partFormula_target root children part output built target member
  apply (target_exact env root children target term refinement found observed _).mpr
  simp [extractedValue, found]

/-- Satisfies translates mathematical entailment from the actual observed refinement. -/
theorem satisfies_entailment (env : Name → Int) (root : Formula) (children : List (Option Formula))
    (target : SourceGuards.Path) (requirement refinement output : Formula)
    (built : partFormula root children (.satisfies target requirement) = .ok output)
    (observed : targetRefinement root children target = some refinement) :
    Holds integerModel env output ↔
      ∀ value, Holds integerModel (update env valueName value) refinement →
        Holds integerModel (update env valueName value) requirement := by
  obtain ⟨term, found⟩ := partFormula_target root children (.satisfies target requirement) output built
    target (by simp [SourceGuards.paths])
  rw [partFormula_derived env root children (.satisfies target requirement) output built]
  simp only [actualGuard, extractedValue, found, Option.map_some, Option.getD_some]
  simp only [target_exact env root children target term refinement found observed]
  simp

/-- A canonical filled integer label admits exactly its displayed integer under every ambient environment. -/
theorem literal_refinement (env : Name → Int) (actual candidate : Int) :
    Holds integerModel (update env valueName candidate) (IntegerLiteral.refinement valueName actual) ↔
      candidate = actual := by
  simp [IntegerLiteral.refinement, Holds, evaluateTerm, integerModel, CoreFormula.evalRelation, update]

/-- Satisfies on a filled exact label is mathematical implication from that singleton refinement. -/
theorem actual_satisfies (env : Name → Int) (values : SourceGuards.Path → Int)
    (target : SourceGuards.Path) (requirement : Formula) :
    actualGuard env values (.satisfies target requirement) ↔
      ∀ candidate, Holds integerModel (update env valueName candidate)
        (IntegerLiteral.refinement valueName (values target)) →
        Holds integerModel (update env valueName candidate) requirement := by
  simp [actualGuard, literal_refinement]

/-- Canonical exact roots discharge both refinement truth and extracted-value independence. -/
theorem literal_roots_exact (env : Name → Int) (root : Formula) (children : List (Option Formula))
    (values : SourceGuards.Path → Int) (part : SourceGuards.Guard Formula) (output : Formula)
    (built : partFormula root children part = .ok output)
    (exactRoots : ∀ target ∈ SourceGuards.paths part,
      targetRefinement root children target = some (IntegerLiteral.refinement valueName (values target))) :
    Holds integerModel env output ↔ actualGuard env values part := by
  apply partFormula_exact env root children values part output built
  intro target member refinement found
  have same := Option.some.inj ((exactRoots target member).symm.trans found)
  rw [← same]
  exact (literal_refinement env (values target) (values target)).mpr rfl

/-- The source traverses the selected open guards in order before constructing their conjunction. -/
def partFormulas (root : Formula) (children : List (Option Formula)) :
    List (SourceGuards.Guard Formula) → Except TranslationError (List Formula)
  | [] => .ok []
  | part :: rest => do
      let formula ← partFormula root children part
      let formulas ← partFormulas root children rest
      pure (formula :: formulas)

/-- A successful guard prefix cannot hide the first later translation error. -/
theorem partFormulas_first_error (root : Formula) (children : List (Option Formula))
    (initial : List (SourceGuards.Guard Formula)) (outputs : List Formula)
    (prefixBuilt : partFormulas root children initial = .ok outputs)
    (part : SourceGuards.Guard Formula) (rest : List (SourceGuards.Guard Formula)) (error : TranslationError)
    (failed : partFormula root children part = .error error) :
    partFormulas root children (initial ++ part :: rest) = .error error := by
  induction initial generalizing outputs with
  | nil => simp [partFormulas, failed, Bind.bind, Except.bind]
  | cons first tail ih =>
      cases head : partFormula root children first with
      | error error => simp [partFormulas, head, Bind.bind, Except.bind] at prefixBuilt
      | ok formula =>
          cases remaining : partFormulas root children tail with
          | error error => simp [partFormulas, head, remaining, Bind.bind, Except.bind] at prefixBuilt
          | ok formulas => simp [partFormulas, head, ih formulas remaining, Bind.bind, Except.bind]

/-- Successful traversal pairs each original guard with its actual translated formula. -/
theorem partFormulas_rows (root : Formula) (children : List (Option Formula))
    (parts : List (SourceGuards.Guard Formula)) (outputs : List Formula)
    (built : partFormulas root children parts = .ok outputs) :
    Language.All₂ (fun part output => partFormula root children part = .ok output) parts outputs := by
  induction parts generalizing outputs with
  | nil => cases built; exact .nil
  | cons part rest ih =>
      cases head : partFormula root children part with
      | error error => simp [partFormulas, head, Bind.bind, Except.bind] at built
      | ok formula =>
          cases tail : partFormulas root children rest with
          | error error => simp [partFormulas, head, tail, Bind.bind, Except.bind] at built
          | ok formulas =>
              have same : outputs = formula :: formulas := by
                simpa [partFormulas, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using built.symm
              subst outputs
              exact .cons head (ih formulas tail)

/-- All translated formulas hold exactly when all selected open guards hold on the actual values. -/
theorem partFormulas_exact (env : Name → Int) (root : Formula) (children : List (Option Formula))
    (values : SourceGuards.Path → Int) (parts : List (SourceGuards.Guard Formula)) (outputs : List Formula)
    (built : partFormulas root children parts = .ok outputs)
    (refined : ∀ part ∈ parts, ∀ target ∈ SourceGuards.paths part, ∀ refinement,
      targetRefinement root children target = some refinement →
        Holds integerModel (update env valueName (values target)) refinement) :
    (∀ output ∈ outputs, Holds integerModel env output) ↔
      ∀ part ∈ parts, actualGuard env values part := by
  have rows := partFormulas_rows root children parts outputs built
  clear built
  induction rows with
  | nil => simp
  | @cons part output parts outputs head tail ih =>
      have first := partFormula_exact env root children values part output head
        (refined part (by simp))
      have rest := ih (fun part member => refined part (by simp [member]))
      simpa only [List.forall_mem_cons] using and_congr first rest

/-- The complete parent formula retains child constraints and exactly the translated open guard conditions. -/
theorem parent_formula_exact (tuple : List Int) (keys : List OpenIntegerKeys.Key)
    (root : Formula) (children : List (Option Formula))
    (values : SourceGuards.Path → Int) (parts : List (SourceGuards.Guard Formula)) (outputs : List Formula)
    (built : partFormulas root children parts = .ok outputs)
    (refined : ∀ part ∈ parts, ∀ target ∈ SourceGuards.paths part, ∀ refinement,
      targetRefinement root children target = some refinement →
        Holds integerModel (update (OpenIntegerKeys.tupleEnv tuple) valueName (values target)) refinement) :
    Holds integerModel (OpenIntegerKeys.tupleEnv tuple)
        (ParentIntegerSettlement.restrictedFormula keys outputs) ↔
      Holds integerModel (OpenIntegerKeys.tupleEnv tuple) (OpenIntegerKeys.join keys).formula ∧
      ∀ part ∈ parts, actualGuard (OpenIntegerKeys.tupleEnv tuple) values part := by
  rw [ParentIntegerSettlement.restrictedFormula_exact,
    partFormulas_exact (OpenIntegerKeys.tupleEnv tuple) root children values parts outputs built refined]

/-- Negated open guards are not silently treated as one of the two supported source forms. -/
theorem unsupported_not (root : Formula) (children : List (Option Formula)) (part : SourceGuards.Guard Formula) :
    partFormula root children (.not part) = .error (.integerRead (.not part)) := rfl

end MicroCFTA.ParentGuardFormula
