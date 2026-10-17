import MicroCFTA.SourceCurrentConjunctionProjectionResources
import MicroCFTA.SourceCurrentConjunctionRequirements

/-!
# Initial resources for current conjunction class requirements

The original forest count, child width, and equality shape fix every job
bound before the first class. Each class uses the preceding actual heap.
One common pair of fuels executes the same literal complete class worker.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRequirements (ClassRequirements RowsReady canonical)
open SourceCurrentConjunctionCompletionReads (Projections jobs)
open SourceCurrentConjunctionProjectionResources (jobsBound workerFuel Replay)
open HeightOrderControlled (iterate)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Each class uses the original forest and path occurrence ceilings. -/
def forecast (shape width count classes resource : Nat) : Nat :=
  iterate (jobsBound shape width (count * shape)) classes resource

/-- The whole class sequence retains its initial scalar. -/
theorem forecast_ge (shape width count classes resource : Nat) :
    resource ≤ forecast shape width count classes resource :=
  SourceCurrentMemoMergeNumericControl.iterate_ge _
    (SourceCurrentConjunctionProjectionResources.jobsBound_ge shape width (count * shape)) classes resource

/-- Larger initial resources retain the complete fixed class schedule. -/
theorem forecast_mono (shape width count classes : Nat) {first last : Nat} (increase : first ≤ last) :
    forecast shape width count classes first ≤ forecast shape width count classes last :=
  SourceCurrentMemoMergeNumericControl.iterate_mono _
    (SourceCurrentConjunctionProjectionResources.jobsBound_mono shape width (count * shape)) classes increase

/-- Additional original classes retain every shorter class sequence. -/
theorem forecast_count_mono (shape width count : Nat) {first last : Nat} (increase : first ≤ last) (resource : Nat) :
    forecast shape width count first resource ≤ forecast shape width count last resource :=
  SourceCurrentMemoMergeNumericControl.iterate_count_mono _
    (SourceCurrentConjunctionProjectionResources.jobsBound_ge shape width (count * shape)) increase resource

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Resident closed canonicalization retains at most the original number of occurrences. -/
theorem canonical_length (values : List (Value Symbol Guard)) (heap : State Symbol Guard)
    (semantic : SemanticReady heap) (available : Values heap values) (closed : ClosedValues values) :
    (canonical values).length ≤ values.length := by
  classical
  rw [SourceCurrentConjunctionRequirements.canonical_exact values heap semantic available closed]
  unfold SourceCurrentConjunctionEmptinessRows.conjunction
  split
  · rename_i member
    have positive := List.length_pos_of_mem member
    simpa only [List.length_singleton] using positive
  · simpa only [List.length_mergeSort] using List.length_eraseDups_le values

/-- The exact common-fuel projection certificate executes the literal physical job worker. -/
theorem projections_replay {work reader : Nat}
    {inputs : List (SourceCurrentConjunctionCompletionReads.Job Symbol Guard)}
    {before after : State Symbol Guard} {values : List (Value Symbol Guard)}
    {actual : Projections inputs before values after} (ready : Replay work reader actual)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    SourceCurrentConjunctionRowsWorker.projections work reader inputs ⟨before, operations⟩ =
      .done values ⟨after, operations⟩ := by
  induction ready with
  | nil => rfl
  | cons done tail ih =>
      simp only [SourceCurrentConjunctionRowsWorker.projections, done, ih,
        SourceCurrentConjunctionRowsWorker.Outcome.bind]

private theorem exact_classes {forests : List (List (Value Symbol Guard))}
    {constraints : EqualityNormalize.Constraints} {before after : State Symbol Guard}
    {requirements : List (List (Value Symbol Guard))}
    (actual : ClassRequirements forests constraints before requirements after)
    (shape width count resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : RowsReady before forests) (fits : Fits resource before)
    (forestCount : forests.length ≤ count) (widths : ∀ forest ∈ forests, forest.length ≤ width)
    (pathCounts : ∀ paths ∈ constraints, paths.length ≤ shape)
    (depths : ∀ paths ∈ constraints, ∀ path ∈ paths, path.length ≤ shape) :
    Fits (forecast shape width count constraints.length resource) after ∧
      (∀ row ∈ requirements, row.length ≤ count * shape) ∧
      (∀ operations work reader, workerFuel shape ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (forecast shape width count constraints.length resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.classes work reader forests constraints ⟨before, operations⟩ =
          .done requirements ⟨after, operations⟩) := by
  induction actual generalizing resource with
  | nil => exact ⟨fits, by simp, by intros; rfl⟩
  | @cons paths before projected middle constraints requirements after first rest ih =>
      have jobInputs := SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
        (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2)
      have jobDepths : ∀ job ∈ jobs forests paths, job.2.length ≤ shape := by
        intro job member
        obtain ⟨forest, _, included⟩ := List.mem_flatMap.mp member
        obtain ⟨path, pathIn, rfl⟩ := List.mem_map.mp included
        exact depths paths List.mem_cons_self path pathIn
      have jobWidths : ∀ job ∈ jobs forests paths, job.1.length ≤ width := by
        intro job member
        obtain ⟨forest, forestIn, included⟩ := List.mem_flatMap.mp member
        obtain ⟨path, _, rfl⟩ := List.mem_map.mp included
        exact widths forest forestIn
      have jobCount : (jobs forests paths).length ≤ count * shape := by
        rw [SourceCurrentConjunctionCompletionReads.jobs_length]
        exact Nat.mul_le_mul forestCount (pathCounts paths List.mem_cons_self)
      have one := SourceCurrentConjunctionProjectionResources.Projections.bound first shape width
        (count * shape) resource semantic costs jobInputs fits jobDepths jobWidths jobCount
      have physical := first.verified (fun _ => True) semantic costs (by intros; trivial) jobInputs
      have tail := ih (jobsBound shape width (count * shape) resource) physical.1.semantic physical.1.costs
        (fun forest member => ⟨fun value included => physical.1.keeps.available value ((inputs forest member).1 value included),
          (inputs forest member).2⟩) one.1 forestCount widths
        (fun paths member => pathCounts paths (List.mem_cons_of_mem _ member))
        (fun paths member => depths paths (List.mem_cons_of_mem _ member))
      have larger := forecast_ge shape width count constraints.length (jobsBound shape width (count * shape) resource)
      have headWidth := canonical_length projected middle physical.1.semantic physical.2.1 physical.2.2
      rw [one.2.1] at headWidth
      refine ⟨tail.1, ?_, ?_⟩
      · intro row member
        rcases List.mem_cons.mp member with rfl | member
        · exact Nat.le_trans headWidth jobCount
        · exact tail.2.1 row member
      · intro operations work reader enoughWork enoughRead
        have firstReady := one.2.2.mono enoughWork
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono larger) enoughRead)
        have firstDone := projections_replay firstReady operations
        have tailDone := tail.2.2 operations work reader enoughWork enoughRead
        simp only [SourceCurrentConjunctionRowsWorker.classes, firstDone, tailDone,
          SourceCurrentConjunctionRowsWorker.Outcome.bind]

/-- Original equality-shape and forest limits bound the complete actual class graph. -/
theorem classes_bound {forests : List (List (Value Symbol Guard))}
    {constraints : EqualityNormalize.Constraints} {before after : State Symbol Guard}
    {requirements : List (List (Value Symbol Guard))}
    (actual : ClassRequirements forests constraints before requirements after)
    (shape width count resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : RowsReady before forests) (fits : Fits resource before)
    (forestCount : forests.length ≤ count) (widths : ∀ forest ∈ forests, forest.length ≤ width)
    (classes : constraints.length ≤ shape) (pathCounts : ∀ paths ∈ constraints, paths.length ≤ shape)
    (depths : ∀ paths ∈ constraints, ∀ path ∈ paths, path.length ≤ shape) :
    Fits (forecast shape width count shape resource) after ∧ requirements.length = constraints.length ∧
      (∀ row ∈ requirements, row.length ≤ count * shape) ∧
      (∀ operations work reader, workerFuel shape ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (forecast shape width count shape resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.classes work reader forests constraints ⟨before, operations⟩ =
          .done requirements ⟨after, operations⟩) := by
  have own := exact_classes actual shape width count resource semantic costs inputs fits forestCount widths pathCounts depths
  have larger := forecast_count_mono shape width count classes resource
  exact ⟨own.1.mono larger, actual.length, own.2.1,
    fun operations work reader enoughWork enoughRead => own.2.2 operations work reader enoughWork
      (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono larger) enoughRead)⟩

/-- Initial forests and equality shape construct their own class requirements and numeric worker return. -/
theorem complete (annotation : Guard → Prop) (forests : List (List (Value Symbol Guard)))
    (constraints : EqualityNormalize.Constraints) (before : State Symbol Guard)
    (shape width count resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (fields : SourceEqualityAnnotationHeap.Heap annotation before)
    (inputs : RowsReady before forests) (fits : Fits resource before)
    (forestCount : forests.length ≤ count) (widths : ∀ forest ∈ forests, forest.length ≤ width)
    (classes : constraints.length ≤ shape) (pathCounts : ∀ paths ∈ constraints, paths.length ≤ shape)
    (depths : ∀ paths ∈ constraints, ∀ path ∈ paths, path.length ≤ shape) :
    ∃ requirements after, ClassRequirements forests constraints before requirements after ∧
      SourceCurrentConjunctionCompletionReads.Effects annotation before after ∧ RowsReady after requirements ∧
      Fits (forecast shape width count shape resource) after ∧ requirements.length = constraints.length ∧
      (∀ row ∈ requirements, row.length ≤ count * shape) ∧
      (∀ operations work reader, workerFuel shape ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (forecast shape width count shape resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.classes work reader forests constraints ⟨before, operations⟩ =
          .done requirements ⟨after, operations⟩) := by
  obtain ⟨requirements, after, actual, effects, ready⟩ :=
    SourceCurrentConjunctionRequirements.classes_complete annotation forests constraints before semantic costs fields inputs
  have own := classes_bound actual shape width count resource semantic costs inputs fits forestCount widths classes pathCounts depths
  exact ⟨requirements, after, actual, effects, ready, own⟩

end MicroCFTA.SourceCurrentConjunctionRequirementResources
