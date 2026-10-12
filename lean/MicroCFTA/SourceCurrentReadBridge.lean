import MicroCFTA.SourceCurrentReadTransport

/-!
# Current scoped guard evaluation across planned reads

Both runtime scope checks retain the same result across the constructed
lossless name map. Ambiguous tables are permitted. The backend spelling
contract is separate from the later many-to-one logical query theorem.
-/
namespace MicroCFTA.SourceCurrentReadBridge
open FullSyntax SourceFormula SourceScopeStack

/-- A nested guard reads only the paths and literal requirements of its outer guard. -/
structure Included (outer inner : SourceGuards.Guard Formula) : Prop where
  paths : ∀ path ∈ SourceGuards.paths inner, path ∈ SourceGuards.paths outer
  symbols : ∀ path ∈ SourceGuards.sensitive inner, path ∈ SourceGuards.sensitive outer
  requirements : ∀ formula ∈ SourceGuards.requirements inner, formula ∈ SourceGuards.requirements outer

/-- Retain the exact outer table while evaluating one nested guard. -/
def evaluate (solver : SourceGuards.Entailment Formula) (outer : SourceGuards.Guard Formula)
    (observed : SourceGuards.Observations Formula) (scopes : List Scope) (positive : Bool) (inner : SourceGuards.Guard Formula) : Guards.Verdict :=
  let table := SourceGuards.substitutionValues operations observed (SourceObservations.sameShape operations observed []) outer
  SourceSubstitutionPrecedence.evaluateWith operations solver observed (SourceObservations.sameShape operations observed) table.1 table.2 scopes positive inner

private theorem missing (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (path : SourceGuards.Path)
    (requested : path ∈ SourceGuards.paths guard) (absent : first path = none) : second path = none := by
  have equal := reads.refinements path requested
  rw [absent] at equal
  exact Option.map_eq_none_iff.mp equal.symm

private theorem present (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (path : SourceGuards.Path)
    (requested : path ∈ SourceGuards.paths guard) (value : SourceGuards.Observed Formula) (found : first path = some value) :
    ∃ other, second path = some other ∧ other.refinement = value.refinement := by
  have equal := reads.refinements path requested
  rw [found] at equal
  exact Option.map_eq_some_iff.mp equal.symm

private theorem polarized_names (guard : SourceGuards.Guard Formula) (observed : SourceGuards.Observations Formula)
    (requirement : Formula) (member : requirement ∈ SourceGuards.requirements guard) (positive : Bool) :
    ∀ name ∈ formulaNames (if positive then requirement else operations.negate requirement),
      name ∈ SourceSemanticNames.ambient operations observed guard := by
  cases positive <;> simpa only [Bool.false_eq_true, ↓reduceIte, operations, formulaNames] using
    (requirement_formula_names guard observed requirement member)

/-- Current source guard control agrees across planned reads under the spelling contract. -/
theorem evaluate_equal (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (outer : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads outer first second)
    (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves outer first recipes scopes) (otherResolved : Resolves outer second recipes other)
    (positive : Bool) (inner : SourceGuards.Guard Formula) (included : Included outer inner) :
    evaluate solver outer first scopes positive inner = evaluate solver outer second other positive inner := by
  cases inner with
  | top | bottom => simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith]
  | same left right =>
      have leftRequested := included.symbols left (by simp [SourceGuards.sensitive])
      have rightRequested := included.symbols right (by simp [SourceGuards.sensitive])
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, reads.symbols left leftRequested, reads.symbols right rightRequested,
        SourceScopeSymbols.same outer first second reads recipes scopes other resolved otherResolved left right leftRequested rightRequested]
  | entails left right =>
      have leftRequested := included.paths left (by simp [SourceGuards.paths])
      have rightRequested := included.paths right (by simp [SourceGuards.paths])
      cases leftFound : first left with
      | none => simp [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, leftFound, missing outer first second reads left leftRequested leftFound]
      | some antecedent =>
          obtain ⟨newAntecedent, newLeft, sameLeft⟩ := present outer first second reads left leftRequested antecedent leftFound
          cases rightFound : first right with
          | none => simp [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, leftFound, newLeft, rightFound, missing outer first second reads right rightRequested rightFound]
          | some consequent =>
              obtain ⟨newConsequent, newRight, sameRight⟩ := present outer first second reads right rightRequested consequent rightFound
              simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, leftFound, rightFound, newLeft, newRight, sameLeft, sameRight]
              rw [SourceCurrentReadTransport.ordinary model nullary laws sortDomain solver stable outer first second reads
                recipes scopes other resolved otherResolved antecedent.refinement consequent.refinement
                (observed_formula_names outer first left antecedent leftRequested leftFound)
                (observed_formula_names outer first right consequent rightRequested rightFound)]
  | satisfies target requirement =>
      have requested := included.paths target (by simp [SourceGuards.paths])
      cases found : first target with
      | none => simp [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, found, missing outer first second reads target requested found]
      | some value =>
          obtain ⟨newValue, newFound, same⟩ := present outer first second reads target requested value found
          simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, found, newFound, same]
          exact SourceCurrentReadTransport.ordinary model nullary laws sortDomain solver stable outer first second reads
            recipes scopes other resolved otherResolved value.refinement _
            (observed_formula_names outer first target value requested found)
            (polarized_names outer first requirement (included.requirements requirement (by simp [SourceGuards.requirements])) positive)
  | holds targets requirement =>
      have requested : ∀ path ∈ targets, path ∈ SourceGuards.paths outer := by simpa only [SourceGuards.paths] using included.paths
      have same := SourceReadAgreement.observeMany_refinements first second targets
        (fun path member => reads.refinements path (requested path member))
      cases found : SourceGuards.observeMany first targets with
      | none =>
          rw [found] at same
          have otherMissing := Option.map_eq_none_iff.mp same.symm
          simp [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, found, otherMissing]
      | some values =>
          rw [found] at same
          obtain ⟨otherValues, otherFound, _⟩ := Option.map_eq_some_iff.mp same.symm
          simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith, found, otherFound]
          exact SourceCurrentReadTransport.holds model nullary laws sortDomain solver stable outer first second reads
            recipes scopes other resolved otherResolved targets requested values otherValues found otherFound _
            (polarized_names outer first requirement (included.requirements requirement (by simp [SourceGuards.requirements])) positive)
  | substitute additions inner =>
      have requested : Requested outer additions := by
        intro entry member
        exact ⟨included.symbols entry.actual (by simp [SourceGuards.sensitive]; exact Or.inl ⟨entry, member, by simp⟩),
          included.symbols entry.formal (by simp [SourceGuards.sensitive]; exact Or.inl ⟨entry, member, by simp⟩)⟩
      have smaller : Included outer inner :=
        ⟨fun path member => included.paths path (by simp [SourceGuards.paths, member]),
         fun path member => included.symbols path (by simp [SourceGuards.sensitive, member]),
         by simpa only [SourceGuards.requirements] using included.requirements⟩
      have related := SourceResolvedTables.resolveMany_aligned operations outer first second reads additions requested
      change SourceResolvedTables.OptionRel _ (resolve outer first additions) (resolve outer second additions) at related
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith]
      cases found : resolve outer first additions <;> cases otherFound : resolve outer second additions <;>
        simp only [resolve] at found otherFound related <;>
        simp only [found, otherFound, SourceResolvedTables.OptionRel] at related ⊢
      have policy := SourceCurrentReadTransport.checks _ _ _ scopes other related
        (SourceScopeSymbols.aligned outer first second reads recipes scopes other resolved otherResolved)
      rw [policy]
      split
      · rfl
      · simpa only [evaluate, SourceSubstitutionPrecedence.evaluateWith] using
          (evaluate_equal model nullary laws sortDomain solver stable outer first second reads
            (additions :: recipes) _ _
            (.cons ⟨by simpa only [resolve] using found, requested⟩ resolved)
            (.cons ⟨by simpa only [resolve] using otherFound, requested⟩ otherResolved)
            positive inner smaller)
  | not inner =>
      have smaller : Included outer inner :=
        ⟨by simpa only [SourceGuards.paths] using included.paths,
         by simpa only [SourceGuards.sensitive] using included.symbols,
         by simpa only [SourceGuards.requirements] using included.requirements⟩
      simpa only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith] using
        (evaluate_equal model nullary laws sortDomain solver stable outer first second reads recipes scopes other
          resolved otherResolved (!positive) inner smaller)
  | and parts | or parts =>
      simp only [evaluate, SourceSubstitutionPrecedence.evaluateWith, SourceEnclosingRenames.evaluateWith]
      congr 1
      apply List.map_congr_left
      intro part member
      exact evaluate_equal model nullary laws sortDomain solver stable outer first second reads recipes scopes other
        resolved otherResolved positive part
        ⟨fun path present => included.paths path (by simpa only [SourceGuards.paths] using List.mem_flatMap.mpr ⟨part, member, present⟩),
         fun path present => included.symbols path (by simpa only [SourceGuards.sensitive] using List.mem_flatMap.mpr ⟨part, member, present⟩),
         fun formula present => included.requirements formula (by simpa only [SourceGuards.requirements] using List.mem_flatMap.mpr ⟨part, member, present⟩)⟩
termination_by sizeOf inner


/-- Each public Boolean operand retains the exact repaired sparse verdict under planned reads. -/
theorem public_equal (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (positive : Bool) :
    SourceSubstitutionPrecedence.evaluate operations solver first (SourceObservations.sameShape operations first) positive guard =
      SourceSubstitutionPrecedence.evaluate operations solver second (SourceObservations.sameShape operations second) positive guard := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [SourceSubstitutionPrecedence.evaluate]
      exact evaluate_equal model nullary laws sortDomain solver stable _ first second reads [] [] [] .nil .nil positive _
        ⟨fun _ member => member, fun _ member => member, fun _ member => member⟩
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [SourceSubstitutionPrecedence.evaluate]
          exact public_equal model nullary laws sortDomain solver stable inner first second
            (SourceReadAgreement.restrict _ inner first second reads
              (by simp [SourceGuards.paths]) (by simp [SourceGuards.sensitive])) positive
      | cons head tail =>
          simp only [SourceSubstitutionPrecedence.evaluate]
          exact evaluate_equal model nullary laws sortDomain solver stable _ first second reads [] [] [] .nil .nil positive _
            ⟨fun _ member => member, fun _ member => member, fun _ member => member⟩
  | not inner =>
      simp only [SourceSubstitutionPrecedence.evaluate]
      exact public_equal model nullary laws sortDomain solver stable inner first second
        (SourceReadAgreement.restrict _ inner first second reads
          (by simp [SourceGuards.paths]) (by simp [SourceGuards.sensitive])) (!positive)
  | and parts | or parts =>
      simp only [SourceSubstitutionPrecedence.evaluate]
      congr 1
      apply List.map_congr_left
      intro part member
      exact public_equal model nullary laws sortDomain solver stable part first second
        (SourceReadAgreement.restrict _ part first second reads
          (fun path present => by simpa only [SourceGuards.paths] using List.mem_flatMap.mpr ⟨part, member, present⟩)
          (fun path present => by simpa only [SourceGuards.sensitive] using List.mem_flatMap.mpr ⟨part, member, present⟩)) positive
termination_by sizeOf guard

/-- A successful sparse planned-read cell certifies complete mathematical guard satisfaction. -/
theorem cell_yes (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : Name → Value → Prop)
    (solver : SourceGuards.Entailment Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : SourceGuards.Guard Formula) (cell : SourceGuards.Observations Formula)
    (term : Language.Term (SourceObservations.Label Formula))
    (reads : SourceReadAgreement.Reads guard cell (SourceObservations.observe term))
    (sound : ∀ context, SourceEntailment.Sound model (SourceQuotientQueries.SolverDomain sortDomain term context) solver)
    (yes : SourceSubstitutionPrecedence.evaluateGuardWithShape operations solver cell guard = .yes) :
    SourceQuotientGuards.Public model sortDomain term true guard := by
  apply SourceQuotientGuards.public_yes model nullary laws sortDomain solver term sound true guard
  exact (public_equal model nullary laws sortDomain solver stable guard cell (SourceObservations.observe term) reads true).symm.trans yes

end MicroCFTA.SourceCurrentReadBridge
