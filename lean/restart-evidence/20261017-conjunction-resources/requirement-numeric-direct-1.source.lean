import MicroCFTA.SourceCurrentConjunctionRequirementResources

/-!
# Numeric complete requirements of current conjunction tuples

Literal child columns precede class projections. The original tuple length,
child width, and equality shape bound both parts of the returned worklist.
The initial producer constructs its own complete requirements graph.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRequirements (Requirements RowsReady columns arity canonical)
open SourceCurrentConjunctionRequirementResources (forecast canonical_length classes_bound)
open SourceCurrentConjunctionProjectionResources (workerFuel)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Every child column has at most one occurrence per original tuple edge. -/
theorem column_width (rows : List (List A)) (width : Nat) (column : List A)
    (member : column ∈ MergedAlternativesGroups.columns rows width) : column.length ≤ rows.length := by
  induction width generalizing rows with
  | zero => cases member
  | succ width ih =>
      rcases List.mem_cons.mp member with same | member
      · rw [same]
        exact List.length_filterMap_le List.head? rows
      · simpa only [List.length_map] using ih (rows.map List.tail) member

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Original tuple resources bound the complete actual requirements and its literal worker. -/
theorem bound {tuple : List (EdgeValue Symbol Guard)} {constraints : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Requirements tuple constraints before requirements after)
    (shape width count resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) (fits : Fits resource before)
    (tupleCount : tuple.length ≤ count) (widths : ∀ edge ∈ tuple, edge.children.length ≤ width)
    (arityBound : arity tuple ≤ width) (classes : constraints.length ≤ shape)
    (pathCounts : ∀ paths ∈ constraints, paths.length ≤ shape)
    (depths : ∀ paths ∈ constraints, ∀ path ∈ paths, path.length ≤ shape) :
    Fits (forecast shape width count shape resource) after ∧
      requirements.length ≤ width + shape ∧
      (∀ row ∈ requirements, row.length ≤ count + count * shape) ∧
      (∀ operations work reader, workerFuel shape ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (forecast shape width count shape resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.requirements work reader tuple constraints ⟨before, operations⟩ =
          .done requirements ⟨after, operations⟩) := by
  have length := actual.length
  cases actual with
  | run _ actual =>
      have inputs := SourceCurrentConjunctionRequirements.tuple_inputs tuple before semantic resident closed
      have forestCount : (tuple.map EdgeValue.children).length ≤ count := by simpa only [List.length_map] using tupleCount
      have forestWidths : ∀ forest ∈ tuple.map EdgeValue.children, forest.length ≤ width := by
        intro forest member
        obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
        exact widths edge included
      have own := classes_bound actual shape width count resource semantic costs inputs fits
        forestCount forestWidths classes pathCounts depths
      refine ⟨own.1, by omega, ?_, ?_⟩
      · intro row member
        rcases List.mem_append.mp member with column | member
        · obtain ⟨original, included, rfl⟩ := List.mem_map.mp column
          have ready := SourceCurrentConjunctionRequirements.columns_ready tuple before semantic resident closed original included
          have canonical := canonical_length original before semantic ready.1 ready.2
          have width := column_width (tuple.map EdgeValue.children) (arity tuple) original included
          simp only [List.length_map] at width
          omega
        · have width := own.2.2.1 row member
          omega
      · intro operations work reader enoughWork enoughRead
        have done := own.2.2.2 operations work reader enoughWork enoughRead
        simp only [SourceCurrentConjunctionRowsWorker.requirements, done,
          SourceCurrentConjunctionRowsWorker.Outcome.bind]

/-- Initial resident tuple data constructs its complete numeric requirements without a future return. -/
theorem complete (annotation : Guard → Prop) (tuple : List (EdgeValue Symbol Guard))
    (constraints : EqualityNormalize.Constraints) (before : State Symbol Guard)
    (shape width count resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (fields : SourceEqualityAnnotationHeap.Heap annotation before) (resident : Edges before tuple)
    (closed : ClosedEdges tuple) (sameArity : SourceCurrentConjunctionRequirements.SameArity tuple)
    (fits : Fits resource before) (tupleCount : tuple.length ≤ count)
    (widths : ∀ edge ∈ tuple, edge.children.length ≤ width) (arityBound : arity tuple ≤ width)
    (classes : constraints.length ≤ shape) (pathCounts : ∀ paths ∈ constraints, paths.length ≤ shape)
    (depths : ∀ paths ∈ constraints, ∀ path ∈ paths, path.length ≤ shape) :
    ∃ requirements after, Requirements tuple constraints before requirements after ∧
      SourceCurrentConjunctionCompletionReads.Effects annotation before after ∧ RowsReady after requirements ∧
      Fits (forecast shape width count shape resource) after ∧ requirements.length ≤ width + shape ∧
      (∀ row ∈ requirements, row.length ≤ count + count * shape) ∧
      (∀ operations work reader, workerFuel shape ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (forecast shape width count shape resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.requirements work reader tuple constraints ⟨before, operations⟩ =
          .done requirements ⟨after, operations⟩) := by
  obtain ⟨requirements, after, actual, effects, ready⟩ :=
    SourceCurrentConjunctionRequirements.complete annotation tuple constraints before semantic costs fields resident closed sameArity
  have own := bound actual shape width count resource semantic costs resident closed fits
    tupleCount widths arityBound classes pathCounts depths
  exact ⟨requirements, after, actual, effects, ready, own⟩

end MicroCFTA.SourceCurrentConjunctionRequirementNumeric
