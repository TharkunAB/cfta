import MicroCFTA.SourceCurrentConjunctionProjectionResources
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceEqualityAnnotationConstruction
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.ConjunctionProjectionResourceKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConjunctionCompletionReads (Inputs Job Projections Effects)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionProjectionResources

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0], .mk 1 true []])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem constructed : built = .done root heap := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, Outcome.state]
private theorem semantic : SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
private theorem available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
private theorem closed : root.free = [] := by cbv
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap, built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem annotations : SourceEqualityAnnotationHeap.Heap (fun _ : Bool => True) heap := by
  have actual := SourceEqualityAnnotationConstruction.build (fun _ : Bool => True) expression
    (by simp [expression, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.ManyAllowed, SourceEqualityAnnotationConstruction.EdgesAllowed])
    [] empty (SourceEqualityAnnotationHeap.empty_heap _)
  simpa only [heap, built] using actual
private def q := SourceCurrentMemoMergeResourceControl.initialBound heap.nodes.next heap.edges.next
  (InternedValueMassHeap.initialBound heap)
private theorem initial : Fits q heap :=
  SourceCurrentMemoMergeResourceControl.initial heap _ (InternedValueMassHeap.initial heap semantic.ready.semantic.1.normal.facts)
private def jobs : List (Job Nat Bool) := [([root], [0, 0]), ([root, root], []), ([root], [7, 1])]
private theorem inputs : Inputs heap jobs := by
  simp [Inputs, jobs, InternedNestedProvenance.Values, MergedColdReaderClosedInputs.ClosedValues, available, closed]
private theorem depths : ∀ job ∈ jobs, job.2.length ≤ 2 := by
  intro job member
  simp only [jobs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private theorem counts : ∀ job ∈ jobs, job.1.length ≤ 2 := by
  intro job member
  simp only [jobs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

/-- Initial recursive source construction executes selected, root-union, and missing jobs at shared numeric fuels. -/
theorem constructed_recursive_batch :
    ∃ values after, ∃ actual : Projections jobs heap values after,
      Effects (fun _ : Bool => True) heap after ∧ InternedNestedProvenance.Values after values ∧
      MergedColdReaderClosedInputs.ClosedValues values ∧ Fits (jobsBound 2 2 5 q) after ∧
      values.length = jobs.length ∧ Replay (workerFuel 2) (readerFuel 2 2 5 q) actual := by
  exact complete (fun _ : Bool => True) jobs heap 2 2 5 q semantic costs annotations inputs initial depths counts (by decide)

/-- The same batch keeps all exact intermediate returns at independently larger worker and reader fuels. -/
theorem constructed_larger_replay (workExtra readExtra : Nat) :
    ∃ values after, ∃ actual : Projections jobs heap values after,
      Fits (jobsBound 2 2 5 q) after ∧
      Replay (workerFuel 2 + workExtra) (readerFuel 2 2 5 q + readExtra) actual ∧
      values.length = 3 := by
  obtain ⟨values, after, actual, _effects, _available, _closed, fits, length, ready⟩ := constructed_recursive_batch
  exact ⟨values, after, actual, fits, ready.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _), length⟩
end MicroCFTA.ConjunctionProjectionResourceKernels
#print axioms MicroCFTA.ConjunctionProjectionResourceKernels.constructed_recursive_batch
#check @MicroCFTA.ConjunctionProjectionResourceKernels.constructed_recursive_batch
#print MicroCFTA.ConjunctionProjectionResourceKernels.constructed_recursive_batch
#print axioms MicroCFTA.ConjunctionProjectionResourceKernels.constructed_larger_replay
#check @MicroCFTA.ConjunctionProjectionResourceKernels.constructed_larger_replay
#print MicroCFTA.ConjunctionProjectionResourceKernels.constructed_larger_replay
