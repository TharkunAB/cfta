import MicroCFTA.LatticeDeclaredNames

/-!
# Defining expressions used by parent integer guards

The public extractor reads one outer equality without an occurs check.
The compiler callers reject extracted expressions that mention the refined
value. Accepted caller expressions determine that value in the ambient environment.
-/
namespace MicroCFTA.DefiningTerm
open FullSyntax

/-- The source first accepts `value = term`, then the reverse orientation. -/
def definingTerm : Formula → Option Term
  | .atom .eq left right =>
      if left = .var SourceGuards.valueName then some right
      else if right = .var SourceGuards.valueName then some left
      else none
  | _ => none

/-- `termOf` prefers a unique lattice point, then rejects self-dependent extraction. -/
def termOf (formula : Formula) : Option Term :=
  match LatticeSingleton.onlyPoint SourceGuards.valueName formula with
  | some value => some (.lit value)
  | none => do
      let term ← definingTerm formula
      if SourceGuards.valueName ∈ termNames term then none else some term

/-- The source freeNames check on term == 0 is exactly term-name exclusion. -/
theorem independence_check (term : Term) :
    SourceGuards.valueName ∉ formulaNames (.atom .eq term (.lit 0)) ↔
      SourceGuards.valueName ∉ termNames term := by
  simp [formulaNames, termNames]

/-- A successful fallback retains its exact extracted term and proves value independence. -/
theorem termOf_fallback (formula : Formula) (term : Term)
    (single : LatticeSingleton.onlyPoint SourceGuards.valueName formula = none)
    (found : termOf formula = some term) :
    definingTerm formula = some term ∧ SourceGuards.valueName ∉ termNames term := by
  cases extracted : definingTerm formula with
  | none => simp [termOf, single, extracted] at found
  | some result =>
      by_cases dependent : SourceGuards.valueName ∈ termNames result
      · simp [termOf, single, extracted, dependent] at found
      · have same : result = term := by simpa [termOf, single, extracted, dependent] using found
        subst result
        exact ⟨rfl, dependent⟩

/-- Every successful current caller extraction is independent of the refined value. -/
theorem termOf_independent (formula : Formula) (term : Term) (found : termOf formula = some term) :
    SourceGuards.valueName ∉ termNames term := by
  cases single : LatticeSingleton.onlyPoint SourceGuards.valueName formula with
  | none => exact (termOf_fallback formula term single found).2
  | some value =>
      have same : term = .lit value := by simpa [termOf, single] using found.symm
      simp [same, termNames]

/-- Every returned expression comes from one of the source's two outer equality shapes. -/
theorem definingTerm_cases (formula : Formula) (term : Term) (found : definingTerm formula = some term) :
    formula = .atom .eq (.var SourceGuards.valueName) term ∨
      formula = .atom .eq term (.var SourceGuards.valueName) := by
  cases formula with
  | atom relation left right =>
      cases relation <;> simp only [definingTerm] at found <;> try contradiction
      split at found
      · rename_i same
        cases found
        exact Or.inl (by rw [same])
      · split at found
        · rename_i same
          cases found
          exact Or.inr (by rw [same])
        · cases found
  | _ => simp [definingTerm] at found

/-- A defining equality gives the actual value under every environment satisfying the refinement. -/
theorem definingTerm_sound (model : Interpretation Value)
    (equality : ∀ left right, model.relation .eq left right ↔ left = right)
    (env : Name → Value) (formula : Formula) (term : Term)
    (found : definingTerm formula = some term) (holds : Holds model env formula) :
    evaluateTerm model env term = env SourceGuards.valueName := by
  rcases definingTerm_cases formula term found with rfl | rfl
  · simp only [Holds, evaluateTerm] at holds
    exact ((equality _ _).mp holds).symm
  · simp only [Holds, evaluateTerm] at holds
    exact (equality _ _).mp holds

/-- Updating the refined value cannot change an expression that does not mention it. -/
theorem term_update_absent (model : Interpretation Value) (env : Name → Value)
    (term : Term) (value : Value) (independent : SourceGuards.valueName ∉ termNames term) :
    evaluateTerm model (update env SourceGuards.valueName value) term = evaluateTerm model env term := by
  apply FormulaSemantics.term_ext
  intro name member
  have different : name ≠ SourceGuards.valueName := by intro same; exact independent (same ▸ member)
  simp [update, different]

/-- A self-independent defining expression determines at most one refined value for each ambient environment. -/
theorem definingTerm_unique (model : Interpretation Value)
    (equality : ∀ left right, model.relation .eq left right ↔ left = right)
    (env : Name → Value) (formula : Formula) (term : Term)
    (found : definingTerm formula = some term) (independent : SourceGuards.valueName ∉ termNames term)
    (left right : Value)
    (leftHolds : Holds model (update env SourceGuards.valueName left) formula)
    (rightHolds : Holds model (update env SourceGuards.valueName right) formula) : left = right := by
  have first := definingTerm_sound model equality (update env SourceGuards.valueName left) formula term found leftHolds
  have second := definingTerm_sound model equality (update env SourceGuards.valueName right) formula term found rightHolds
  rw [term_update_absent model env term left independent] at first
  rw [term_update_absent model env term right independent] at second
  simpa [update] using first.symm.trans second

/-- Value independence makes the extracted outer equality an exact value definition. -/
theorem definingTerm_exact (model : Interpretation Value)
    (equality : ∀ left right, model.relation .eq left right ↔ left = right)
    (env : Name → Value) (formula : Formula) (term : Term)
    (found : definingTerm formula = some term) (independent : SourceGuards.valueName ∉ termNames term)
    (value : Value) :
    Holds model (update env SourceGuards.valueName value) formula ↔ value = evaluateTerm model env term := by
  rcases definingTerm_cases formula term found with rfl | rfl
  · simp only [Holds, evaluateTerm, equality, update, ↓reduceIte]
    exact congrArg (value = ·) (term_update_absent model env term value independent) |>.to_iff
  · simp only [Holds, evaluateTerm, equality, update, ↓reduceIte]
    rw [term_update_absent model env term value independent]
    exact eq_comm

/-- The source permits a self-dependent expression and therefore does not assert uniqueness by extraction. -/
theorem self_definition_not_unique :
    let formula := Formula.atom .eq (.var SourceGuards.valueName) (.var SourceGuards.valueName)
    definingTerm formula = some (.var SourceGuards.valueName) ∧
      Holds integerModel (fun _ => 0) formula ∧ Holds integerModel (fun _ => 1) formula := by
  simp [definingTerm, Holds, evaluateTerm, integerModel, CoreFormula.evalRelation]

/-- A successful singleton reader contains an actual successful public lattice table. -/
theorem onlyPoint_table (formula : Formula) (value : Int)
    (found : LatticeSingleton.onlyPoint SourceGuards.valueName formula = some value) :
    ∃ points, LatticeAPI.points [SourceGuards.valueName] (lowerFormula formula) = .ok points := by
  cases built : LatticeAPI.points [SourceGuards.valueName] (lowerFormula formula) with
  | error error => simp [LatticeSingleton.onlyPoint, built] at found
  | ok points => exact ⟨points, rfl⟩

/-- Singleton uniqueness applies to every ambient environment, since successful parsing validates all names. -/
theorem onlyPoint_ambient (env : Name → Int) (formula : Formula) (value : Int)
    (found : LatticeSingleton.onlyPoint SourceGuards.valueName formula = some value)
    (holds : Holds integerModel env formula) : env SourceGuards.valueName = value := by
  obtain ⟨points, built⟩ := onlyPoint_table formula value found
  have scope := LatticeDeclaredNames.points_leafScoped formula points built
  have admitted : LatticeSingleton.Admits SourceGuards.valueName formula (env SourceGuards.valueName) := by
    apply (FormulaSemantics.formula_ext integerModel formula env _ ?_).mp holds
    intro name member
    rw [scope name member]
    simp [LatticeInput.nameValues, LatticeInput.variableOf, OpenIntegerSource.assignTuple_zero]
  exact (LatticeSingleton.onlyPoint_sound SourceGuards.valueName formula value found).2 _ admitted

/-- A successful singleton value satisfies its refinement under every ambient environment. -/
theorem onlyPoint_holds (env : Name → Int) (formula : Formula) (value : Int)
    (found : LatticeSingleton.onlyPoint SourceGuards.valueName formula = some value) :
    Holds integerModel (update env SourceGuards.valueName value) formula := by
  obtain ⟨points, built⟩ := onlyPoint_table formula value found
  have scope := LatticeDeclaredNames.points_leafScoped formula points built
  have accepted := (LatticeSingleton.onlyPoint_sound SourceGuards.valueName formula value found).1
  apply (FormulaSemantics.formula_ext integerModel formula _ _ ?_).mp accepted
  intro name member
  rw [scope name member]
  simp [LatticeInput.nameValues, LatticeInput.variableOf, OpenIntegerSource.assignTuple_zero, update]

/-- The actual onlyPoint-first source extractor always denotes the refined value in its satisfying environment. -/
theorem termOf_sound (env : Name → Int) (formula : Formula) (term : Term)
    (found : termOf formula = some term) (holds : Holds integerModel env formula) :
    evaluateTerm integerModel env term = env SourceGuards.valueName := by
  cases single : LatticeSingleton.onlyPoint SourceGuards.valueName formula with
  | none =>
      exact definingTerm_sound integerModel (by intro left right; simp [integerModel, CoreFormula.evalRelation])
        env formula term (termOf_fallback formula term single found).1 holds
  | some value =>
      have same : term = .lit value := by simpa [termOf, single] using found.symm
      subst term
      simpa [evaluateTerm, integerModel] using (onlyPoint_ambient env formula value single holds).symm

/-- The caller may state refinement truth with its value explicitly assigned. -/
theorem termOf_update (env : Name → Int) (formula : Formula) (term : Term) (value : Int)
    (found : termOf formula = some term)
    (holds : Holds integerModel (update env SourceGuards.valueName value) formula) :
    evaluateTerm integerModel (update env SourceGuards.valueName value) term = value := by
  simpa [update] using termOf_sound (update env SourceGuards.valueName value) formula term found holds

/-- Parent substitution may evaluate the extracted term in the ambient environment when it excludes the refined name. -/
theorem termOf_base (env : Name → Int) (formula : Formula) (term : Term) (value : Int)
    (found : termOf formula = some term) (independent : SourceGuards.valueName ∉ termNames term)
    (holds : Holds integerModel (update env SourceGuards.valueName value) formula) :
    evaluateTerm integerModel env term = value := by
  rw [← term_update_absent integerModel env term value independent]
  exact termOf_update env formula term value found holds

/-- Current compiler extraction supplies the independence required by ambient evaluation. -/
theorem termOf_base_exact (env : Name → Int) (formula : Formula) (term : Term) (value : Int)
    (found : termOf formula = some term)
    (holds : Holds integerModel (update env SourceGuards.valueName value) formula) :
    evaluateTerm integerModel env term = value :=
  termOf_base env formula term value found (termOf_independent formula term found) holds

/-- Every successful repaired extraction is an exact value definition, without a satisfiability premise. -/
theorem termOf_exact (env : Name → Int) (formula : Formula) (term : Term)
    (found : termOf formula = some term) (value : Int) :
    Holds integerModel (update env SourceGuards.valueName value) formula ↔
      value = evaluateTerm integerModel env term := by
  cases single : LatticeSingleton.onlyPoint SourceGuards.valueName formula with
  | none =>
      exact definingTerm_exact integerModel (by intro left right; simp [integerModel, CoreFormula.evalRelation])
        env formula term (termOf_fallback formula term single found).1
        (termOf_independent formula term found) value
  | some result =>
      have same : term = .lit result := by simpa [termOf, single] using found.symm
      subst term
      constructor
      · intro holds
        exact (termOf_base_exact env formula (.lit result) value found holds).symm
      · intro equal
        have sameValue : value = result := by simpa [evaluateTerm, integerModel] using equal
        subst value
        simpa [evaluateTerm, integerModel] using onlyPoint_holds env formula result single

/-- Every accepted compiler measure has exactly one refined value in each ambient environment. -/
theorem termOf_exists_unique (env : Name → Int) (formula : Formula) (term : Term)
    (found : termOf formula = some term) :
    ∃ value, Holds integerModel (update env SourceGuards.valueName value) formula ∧
      ∀ other, Holds integerModel (update env SourceGuards.valueName other) formula → other = value := by
  refine ⟨evaluateTerm integerModel env term, (termOf_exact env formula term found _).mpr rfl, ?_⟩
  intro other holds
  exact (termOf_exact env formula term found other).mp holds

/-- Identity filtering of one value substitution has exactly the ordinary environment-update meaning. -/
theorem single_assignment (model : Interpretation Value) (env : Name → Value) (name : Name) (term : Term) :
    FormulaSubstitution.assignment model env ([(name, term)].filter fun entry => !identityReplacement entry) =
      update env name (evaluateTerm model env term) := by
  have identity : identityReplacement (name, term) = true ↔ term = .var name := by
    cases term with
    | var other =>
        simp only [identityReplacement, beq_iff_eq, Term.var.injEq]
        exact eq_comm
    | _ => simp only [identityReplacement, Bool.false_eq_true, reduceCtorEq]
  by_cases same : term = .var name
  · subst term
    funext queried
    by_cases equal : queried = name <;>
      simp [identityReplacement, FormulaSubstitution.assignment, lookup, update, evaluateTerm, equal]
  · have nonidentity : identityReplacement (name, term) = false := by
      apply Bool.eq_false_iff.mpr
      intro sameIdentity
      exact same (identity.mp sameIdentity)
    funext queried
    by_cases equal : queried = name <;>
      simp [nonidentity, FormulaSubstitution.assignment, lookup, update, equal]

/-- The checked source substitution replaces the value variable by the extracted expression's actual value. -/
theorem value_substitution (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value) (env : Name → Value)
    (predicate : Formula) (term : Term) (output : Formula)
    (substituted : FormulaSubstitution.checked [(SourceGuards.valueName, term)] predicate = .ok output) :
    Holds model env output ↔
      Holds model (update env SourceGuards.valueName (evaluateTerm model env term)) predicate := by
  rw [FormulaCorrectness.checked_semantics model nullary _ _ _ substituted env, single_assignment]

/-- A parent Satisfies translation has the child's concrete refined value when the measure is value-independent. -/
theorem termOf_substitution_exact (env : Name → Int) (refinement predicate : Formula)
    (term : Term) (output : Formula) (value : Int)
    (found : termOf refinement = some term) (independent : SourceGuards.valueName ∉ termNames term)
    (holds : Holds integerModel (update env SourceGuards.valueName value) refinement)
    (substituted : FormulaSubstitution.checked [(SourceGuards.valueName, term)] predicate = .ok output) :
    Holds integerModel env output ↔ Holds integerModel (update env SourceGuards.valueName value) predicate := by
  rw [value_substitution integerModel (by intro value; rfl) env predicate term output substituted,
    termOf_base env refinement term value found independent holds]

/-- Both equality orientations still return the selected expression when both sides happen to be the value variable. -/
theorem definingTerm_left (term : Term) :
    definingTerm (.atom .eq (.var SourceGuards.valueName) term) = some term := by simp [definingTerm]

theorem definingTerm_right (term : Term) :
    definingTerm (.atom .eq term (.var SourceGuards.valueName)) = some term := by
  by_cases same : term = .var SourceGuards.valueName <;> simp [definingTerm, same]

/-- A checked substitution that leaves the refined value alone transports the exact source defining expression. -/
theorem definingTerm_substitute (replacements : List (Name × Term))
    (formula : Formula) (term filled : Term) (found : definingTerm formula = some term)
    (valueUnchanged : lookup SourceGuards.valueName
      (replacements.filter fun entry => !identityReplacement entry) = none)
    (filledTerm : FormulaSubstitution.term
      (replacements.filter fun entry => !identityReplacement entry) term = .ok filled) :
    ∃ output, FormulaSubstitution.checked replacements formula = .ok output ∧ definingTerm output = some filled := by
  rcases definingTerm_cases formula term found with rfl | rfl
  · refine ⟨.atom .eq (.var SourceGuards.valueName) filled, ?_, definingTerm_left filled⟩
    simp [FormulaSubstitution.checked, FormulaSubstitution.formula, FormulaSubstitution.term,
      valueUnchanged, filledTerm, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · refine ⟨.atom .eq filled (.var SourceGuards.valueName), ?_, definingTerm_right filled⟩
    simp [FormulaSubstitution.checked, FormulaSubstitution.formula, FormulaSubstitution.term,
      valueUnchanged, filledTerm, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The source's reserved integer-coordinate prefix never equals its reserved refined-value name. -/
theorem integerName_ne_value (index : Nat) : IntegerLabelCodec.integerName index ≠ SourceGuards.valueName := by
  intro same
  have length := congrArg String.length same
  simp [IntegerLabelCodec.integerName, SourceGuards.valueName] at length
  have longer : "__cfta_value".length < "__cfta_integer_".length := by decide +kernel
  omega

/-- Actual point filling leaves the refined value name unchanged. -/
theorem fill_keeps_value (point : List Int) :
    lookup SourceGuards.valueName
      ((IntegerLabelCodec.replacements point).filter fun entry => !identityReplacement entry) = none := by
  cases found : lookup SourceGuards.valueName
      ((IntegerLabelCodec.replacements point).filter fun entry => !identityReplacement entry) with
  | none => rfl
  | some replacement =>
      have member := FormulaSubstitution.lookup_member _ _ _ found
      have original := (List.mem_filter.mp member).1
      obtain ⟨entry, _, same⟩ := List.mem_map.mp original
      have name := congrArg Prod.fst same
      exact False.elim (integerName_ne_value entry.2 name)

/-- The actual fill replacement list transports the defining expression without an assumed codec inverse. -/
theorem definingTerm_fill (point : List Int) (formula : Formula) (term filled : Term)
    (found : definingTerm formula = some term)
    (filledTerm : FormulaSubstitution.term
      ((IntegerLabelCodec.replacements point).filter fun entry => !identityReplacement entry) term = .ok filled) :
    ∃ output, FormulaSubstitution.checked (IntegerLabelCodec.replacements point) formula = .ok output ∧
      definingTerm output = some filled :=
  definingTerm_substitute (IntegerLabelCodec.replacements point) formula term filled found
    (fill_keeps_value point) filledTerm

/-- The transported expression evaluates under exactly the simultaneous source point assignment. -/
theorem filledTerm_semantics (point : List Int) (term filled : Term)
    (filledTerm : FormulaSubstitution.term
      ((IntegerLabelCodec.replacements point).filter fun entry => !identityReplacement entry) term = .ok filled)
    (env : Name → Int) :
    evaluateTerm integerModel env filled = evaluateTerm integerModel
      (FormulaSubstitution.assignment integerModel env
        ((IntegerLabelCodec.replacements point).filter fun entry => !identityReplacement entry)) term :=
  FormulaCorrectness.term_semantics integerModel (by intro value; rfl) _ term filled filledTerm env

end MicroCFTA.DefiningTerm
