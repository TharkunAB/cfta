import MicroCFTA.SourceCurrentConjunctionTupleBounds
import MicroCFTA.SourceEqualityPCSNativeEdge

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace MicroCFTA.ConjunctionTupleIntegration
open Cache InternedConstructorTemplates EqualityNormalize SourceCurrentConjunctionTupleBounds
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def classes : Constraints := [[[0, 0, 0], [1, 0, 0]]]
private def annotation : Guard := ⟨some classes, .top⟩
private def blocked : Guard := ⟨none, .bottom⟩
private def made : EdgeValue Symbol Guard × State Symbol Guard :=
  run (makeEdge (("pair", .top) : Symbol) annotation [.reference .depth, .reference .depth]) empty
private def edge := made.1
private def rows := [[edge, edge], [edge, edge]]
private def tuple := [edge, edge]
private theorem tuples_exact : SourceCurrentConjunctionTuples.tuples rows = [tuple, tuple, tuple, tuple] := by cbv
private theorem tuple_member : tuple ∈ SourceCurrentConjunctionTuples.tuples rows := by
  rw [tuples_exact]
  exact List.mem_cons_self
private theorem guard_readback : edge.entry.key.constraint = annotation := by cbv
private theorem normalize_fixed (input output : Constraints)
    (prepared : complete (prepare input) = output) (fixed : congruenceStep output = some output) :
    SourceCompactGuards.normalize input = some output := by
  simp only [SourceCompactGuards.normalize, SourceCompactGuards.arrayNormalize_eq,
    mkEqConstraints, EqualityTermination.normalizationBound, EqualityTermination.saturationBound,
    prepared, fixMaybe, fixed, ite_true, SymbolicEqualityBridge.resultClasses]
private theorem combined_live : combined [annotation, annotation] = some classes := by
  have fixed : congruenceStep classes = some classes := by cbv
  have first : SourceCompactGuards.normalize classes = some classes :=
    normalize_fixed classes classes (by cbv) fixed
  have both : SourceCompactGuards.normalize (classes ++ classes) = some classes :=
    normalize_fixed (classes ++ classes) classes (by cbv) fixed
  change SourceCompactGuards.combineEqualities (some classes)
    (SourceCompactGuards.combineEqualities (some classes) (some [])) = some classes
  have tail : SourceCompactGuards.combineEqualities (some classes) (some []) = some classes := by
    simpa only [classes, SourceCompactGuards.combineEqualities, List.append_nil] using first
  rw [tail]
  simpa only [classes, SourceCompactGuards.combineEqualities] using both

/-- Literal allocated edges retain four duplicate tuples and their nontrivial guard path bound. -/
theorem constructed_duplicate_tuples :
    made.2.edges.next = 1 ∧
    SourceCurrentConjunctionTuples.tuples rows = [tuple, tuple, tuple, tuple] ∧
    tuple.length = rows.length ∧ (SourceCurrentConjunctionTuples.tuples rows).length ≤ 2 ^ rows.length ∧
    SourceCurrentConjunctionEmptinessRows.combined (tuple.map SourceCurrentConjunctionCompletionReads.edgeView) = some classes ∧
    classes.length ≤ shapeThrough [annotation] 2 ∧
    (∀ paths ∈ classes, paths.length ≤ shapeThrough [annotation] 2) ∧
    ∀ paths ∈ classes, ∀ path ∈ paths, path.length ≤ shapeThrough [annotation] 2 := by
  have live : SourceCurrentConjunctionEmptinessRows.combined
      (tuple.map SourceCurrentConjunctionEquality.edgeView) = some classes := by
    rw [← combined_edgeView]
    simpa only [tuple, List.map_cons, List.map_nil, guard_readback] using combined_live
  have bounds := tuple_bounds_through [annotation] rows 2 (by decide)
    (by
      intro edges selected entry present
      have sameRows : edges = [edge, edge] := by simpa only [rows, List.mem_cons, List.not_mem_nil, or_false, or_self] using selected
      cases sameRows
      have sameEdge : entry = edge := by simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
      cases sameEdge
      simp only [guard_readback, List.mem_singleton]) tuple tuple_member classes live
  refine ⟨by cbv, tuples_exact, tuple_length rows tuple tuple_member,
    tuples_length_le rows 2 ?_, ?_, bounds⟩
  · intro edges member
    have same : edges = [edge, edge] := by simpa only [rows, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
    cases same
    exact Nat.le_refl _
  · exact (combined_current_edgeView tuple).symm.trans (by
      simpa only [tuple, List.map_cons, List.map_nil, guard_readback] using combined_live)

/-- Initial word enumeration retains order and excludes an actual contradictory combination. -/
theorem ordered_words_and_contradiction :
    words [annotation, blocked] 2 = [[annotation, annotation], [annotation, blocked], [blocked, annotation], [blocked, blocked]] ∧
    combined [annotation, blocked] = none ∧
    combined ([] : List Guard) = some [] ∧
    classShapeBound [annotation, blocked] 2 ≤ shapeThrough [annotation, blocked] 4 := by
  refine ⟨rfl, ?_, rfl, classShapeBound_le_shapeThrough _ 2 4 (by decide)⟩
  rfl
end MicroCFTA.ConjunctionTupleIntegration

#check @MicroCFTA.ConjunctionTupleIntegration.constructed_duplicate_tuples
#print axioms MicroCFTA.ConjunctionTupleIntegration.constructed_duplicate_tuples
#print MicroCFTA.ConjunctionTupleIntegration.constructed_duplicate_tuples
#check @MicroCFTA.ConjunctionTupleIntegration.ordered_words_and_contradiction
#print axioms MicroCFTA.ConjunctionTupleIntegration.ordered_words_and_contradiction
#print MicroCFTA.ConjunctionTupleIntegration.ordered_words_and_contradiction
