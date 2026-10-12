import MicroCFTA.SourceBooleanEntry
import MicroCFTA.SourceFullGuardBridge

/-!
# Current Boolean entry and sparse observations

The global conservative ambiguity gate is sufficient for every independent
scoped atom. Boolean folds preserve the information order, including branches
whose Unknown result does not determine the final decision.
-/
namespace MicroCFTA.SourceBooleanBridge
open SourceGuards SourceObservations SourceGuardRefinement

/-- Restricting the actual-path set cannot add a stored actual observation. -/
theorem actuals_subset (observed : Observations Formula) (outer inner : Guard Formula)
    (included : ∀ path ∈ actualPaths inner, path ∈ actualPaths outer)
    (actual : Actual Formula) (member : actual ∈ actuals observed inner) : actual ∈ actuals observed outer := by
  obtain ⟨path, present, found⟩ := List.mem_filterMap.mp member
  apply List.mem_filterMap.mpr
  exact ⟨path, by simpa [orderedPaths] using included path (by simpa [orderedPaths] using present), found⟩

/-- An ambiguous inner pair would also be an ambiguous pair in the enclosing guard. -/
theorem unambiguous_subset [DecidableEq Formula] (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (outer inner : Guard Formula)
    (included : ∀ path ∈ actualPaths inner, path ∈ actualPaths outer)
    (unambiguous : ambiguous observed sameAt outer = []) : ambiguous observed sameAt inner = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro path member
  obtain ⟨actual, present, target, other, otherPresent, rest⟩ :=
    (SourceActuals.ambiguous_iff observed sameAt inner path).mp member
  have forbidden := (SourceActuals.ambiguous_iff observed sameAt outer path).mpr
    ⟨actual, actuals_subset observed outer inner included actual present, target,
      other, actuals_subset observed outer inner included other otherPresent, rest⟩
  simp [unambiguous] at forbidden

/-- Polarity does not change actual positions. -/
theorem signed_actuals (positive : Bool) (guard : Guard Formula) :
    actualPaths (SourceBooleanEntry.signed positive guard) = actualPaths guard := by
  cases positive <;> simp [SourceBooleanEntry.signed, actualPaths]

theorem signed_unambiguous [DecidableEq Formula] (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (positive : Bool) (guard : Guard Formula)
    (unambiguous : ambiguous observed sameAt guard = []) :
    ambiguous observed sameAt (SourceBooleanEntry.signed positive guard) = [] :=
  unambiguous_subset observed sameAt guard _ (by simp [signed_actuals]) unambiguous

theorem signed_reads (positive : Bool) (guard : Guard Formula) (first second : Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) :
    SourceReadAgreement.Reads (SourceBooleanEntry.signed positive guard) first second := by
  cases positive
  · exact ⟨by simpa [SourceBooleanEntry.signed, paths] using reads.refinements,
      by simpa [SourceBooleanEntry.signed, sensitive] using reads.symbols⟩
  · exact reads

/-- Scoped atoms retain the proved sparse-to-complete information relation in either polarity. -/
theorem scoped_refines [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (term : Language.Term (Label Formula)) (positive : Bool) (guard : Guard Formula)
    (unambiguous : ambiguous (observe term) (sameShape formulas (observe term) []) guard = []) :
    Refines (SourceBooleanEntry.evaluateScoped formulas solver (observe term) (sameShape formulas (observe term)) positive guard)
      (SourceBooleanEntry.evaluateScoped formulas solver (observe term) (sameTerm formulas term) positive guard) :=
  unambiguous_evaluator_refines formulas solver term (SourceBooleanEntry.signed positive guard)
    (signed_unambiguous _ _ positive guard unambiguous)

/-- The repaired dispatcher preserves sparse decisions, even when Unknown occurs in a discarded Boolean branch. -/
theorem evaluate_refines [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (term : Language.Term (Label Formula)) (positive : Bool) (guard : Guard Formula)
    (unambiguous : ambiguous (observe term) (sameShape formulas (observe term) []) guard = []) :
    Refines (SourceBooleanEntry.evaluate formulas solver (observe term) (sameShape formulas (observe term)) positive guard)
      (SourceBooleanEntry.evaluate formulas solver (observe term) (sameTerm formulas term) positive guard) := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [SourceBooleanEntry.evaluate]
      exact scoped_refines formulas solver term positive _ unambiguous
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [SourceBooleanEntry.evaluate]
          exact evaluate_refines formulas solver term positive inner
            (unambiguous_subset _ _ _ inner (by simp [actualPaths]) unambiguous)
      | cons first rest =>
          simp only [SourceBooleanEntry.evaluate]
          exact scoped_refines formulas solver term positive _ unambiguous
  | not inner =>
      simp only [SourceBooleanEntry.evaluate]
      exact evaluate_refines formulas solver term (!positive) inner
        (unambiguous_subset _ _ _ inner (by simp [actualPaths]) unambiguous)
  | and parts | or parts =>
      simp only [SourceBooleanEntry.evaluate]
      apply combine_map_refines
      intro part member
      exact evaluate_refines formulas solver term positive part
        (unambiguous_subset _ _ _ part (fun path present => by
          simpa only [actualPaths] using List.mem_flatMap.mpr ⟨part, member, present⟩) unambiguous)
termination_by sizeOf guard

/-- Exact query transport gives the same scoped atom verdict for equal planned reads. -/
theorem scoped_equal (model : FullSyntax.Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment FullSyntax.Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (positive : Bool) (guard : Guard FullSyntax.Formula) (first second : Observations FullSyntax.Formula)
    (reads : SourceReadAgreement.Reads guard first second)
    (unambiguous : ambiguous first (sameShape SourceFormula.operations first []) guard = []) :
    SourceBooleanEntry.evaluateScoped SourceFormula.operations solver first (sameShape SourceFormula.operations first) positive guard =
      SourceBooleanEntry.evaluateScoped SourceFormula.operations solver second (sameShape SourceFormula.operations second) positive guard :=
  SourceFullGuardBridge.guard_equal model nullary laws sortDomain solver stable (SourceBooleanEntry.signed positive guard)
    first second (signed_reads positive guard first second reads) (signed_unambiguous _ _ positive guard unambiguous)

/-- Planned read agreement transports the complete repaired entry, including arbitrary nested scopes and allocated conflicts. -/
theorem evaluate_equal (model : FullSyntax.Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment FullSyntax.Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (positive : Bool) (guard : Guard FullSyntax.Formula) (first second : Observations FullSyntax.Formula)
    (reads : SourceReadAgreement.Reads guard first second)
    (unambiguous : ambiguous first (sameShape SourceFormula.operations first []) guard = []) :
    SourceBooleanEntry.evaluate SourceFormula.operations solver first (sameShape SourceFormula.operations first) positive guard =
      SourceBooleanEntry.evaluate SourceFormula.operations solver second (sameShape SourceFormula.operations second) positive guard := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ =>
      simp only [SourceBooleanEntry.evaluate]
      exact scoped_equal model nullary laws sortDomain solver stable positive _ first second reads unambiguous
  | substitute additions inner =>
      cases additions with
      | nil =>
          simp only [SourceBooleanEntry.evaluate]
          exact evaluate_equal model nullary laws sortDomain solver stable positive inner first second
            ⟨by simpa [paths] using reads.refinements, by simpa [sensitive] using reads.symbols⟩
            (unambiguous_subset _ _ _ inner (by simp [actualPaths]) unambiguous)
      | cons firstEntry rest =>
          simp only [SourceBooleanEntry.evaluate]
          exact scoped_equal model nullary laws sortDomain solver stable positive _ first second reads unambiguous
  | not inner =>
      simp only [SourceBooleanEntry.evaluate]
      exact evaluate_equal model nullary laws sortDomain solver stable (!positive) inner first second
        ⟨by simpa [paths] using reads.refinements, by simpa [sensitive] using reads.symbols⟩
        (unambiguous_subset _ _ _ inner (by simp [actualPaths]) unambiguous)
  | and parts | or parts =>
      simp only [SourceBooleanEntry.evaluate]
      congr 1
      apply List.map_congr_left
      intro part member
      exact evaluate_equal model nullary laws sortDomain solver stable positive part first second
        (SourceReadAgreement.restrict _ part first second reads
          (fun path present => by simpa only [paths] using List.mem_flatMap.mpr ⟨part, member, present⟩)
          (fun path present => by simpa only [sensitive] using List.mem_flatMap.mpr ⟨part, member, present⟩))
        (unambiguous_subset _ _ _ part (fun path present => by
          simpa only [actualPaths] using List.mem_flatMap.mpr ⟨part, member, present⟩) unambiguous)
termination_by sizeOf guard

/-- Every decided unambiguous sparse cell agrees with each represented complete term at the current public entry. -/
theorem complete_decision (model : FullSyntax.Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (sortDomain : String → Value → Prop)
    (solver : Entailment FullSyntax.Formula) (stable : SourceQueryTransport.Stable model sortDomain solver)
    (guard : Guard FullSyntax.Formula) (cell : Observations FullSyntax.Formula)
    (term : Language.Term (Label FullSyntax.Formula))
    (reads : SourceReadAgreement.Reads guard cell (observe term))
    (unambiguous : ambiguous cell (sameShape SourceFormula.operations cell []) guard = [])
    (decided : SourceBooleanEntry.evaluateGuardWithShape SourceFormula.operations solver cell guard ≠ .unknown) :
    SourceBooleanEntry.evaluateGuardWithShape SourceFormula.operations solver cell guard =
      SourceBooleanEntry.evaluateGuard SourceFormula.operations solver guard term := by
  have equal := evaluate_equal model nullary laws sortDomain solver stable true guard cell (observe term) reads unambiguous
  have refined := evaluate_refines SourceFormula.operations solver term true guard
    (SourceKnownScopes.reads_known guard cell (observe term) reads unambiguous)
  rcases refined with unknown | exact
  · exact False.elim (decided (equal.trans unknown))
  · exact equal.trans exact

end MicroCFTA.SourceBooleanBridge
