import MicroCFTA.SourceEqualityAnnotationProjectionOutcome
import MicroCFTA.SourceCurrentConjunctionRowsWorkerActual

/-!
# Annotation preservation for every raw conjunction-row outcome

Initial physical invariants supply each reached operation.
Failed outcomes retain their actual returned heaps.
-/
namespace MicroCFTA.SourceCurrentConjunctionRowsAnnotationOutcome
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityAnnotationHeap (Heap)
open SourceCurrentConjunctionRowsWorker
variable {Symbol Formula Output : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Both raw outcomes retain annotations at their actual physical heap. -/
def HeapOutcome (annotation : Guard → Prop) (result : Outcome Symbol Formula Output) : Prop :=
  Heap annotation result.state.heap

private theorem bind_heap {Input Output : Type} (annotation : Guard → Prop)
    (first : Outcome Symbol Formula Input)
    (next : Input → Physical Symbol Formula → Outcome Symbol Formula Output)
    (safe : HeapOutcome annotation first)
    (continued : ∀ value after, first = .done value after → HeapOutcome annotation (next value after)) :
    HeapOutcome annotation (first.bind next) := by
  cases first with
  | done value after => exact continued value after rfl
  | failed => exact safe

private theorem map_heap {Input Output : Type} (annotation : Guard → Prop)
    (first : Outcome Symbol Formula Input) (convert : Input → Output)
    (safe : HeapOutcome annotation first) :
    HeapOutcome annotation (first.bind fun value after => .done (convert value) after) := by
  cases first <;> exact safe

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every operand-read outcome retains the original annotation predicate. -/
theorem exposures_heap (annotation : Guard → Prop) (readFuel : Nat)
    (nodes : List (Value Symbol Guard)) (before : Physical Symbol Formula)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (heap : Heap annotation before.heap) :
    HeapOutcome annotation (exposures readFuel nodes before) := by
  induction nodes generalizing before with
  | nil => exact heap
  | cons value values ih =>
      have own := SourceEqualityAnnotationExposure.nodeEdges_heap annotation readFuel value before.heap
        semantic.ready.semantic semantic.ready.covered heap
        (available value List.mem_cons_self) (closed value List.mem_cons_self)
      cases observed : MergedFreshOrdinaryExposure.nodeEdges readFuel value before.heap with
      | done edges middle =>
          have checked := SourceCurrentConjunctionCompletionReads.read_effects annotation
            (SourceEqualityProjectionRead.Read.done readFuel observed) semantic costs heap
            (available value List.mem_cons_self)
          simp only [exposures, observed]
          exact map_heap annotation _ _ (ih ⟨middle, before.equality⟩ checked.semantic checked.costs
            (fun child member => checked.keeps.available child
              (available child (List.mem_cons_of_mem value member)))
            (fun child member => closed child (List.mem_cons_of_mem value member)) checked.annotations)
      | pending key middle =>
          simpa only [exposures, observed, HeapOutcome, Outcome.state, MergedSourceExposure.Result.state] using own
      | unresolved name middle =>
          simpa only [exposures, observed, HeapOutcome, Outcome.state, MergedSourceExposure.Result.state] using own
      | exhausted middle =>
          simpa only [exposures, observed, HeapOutcome, Outcome.state, MergedSourceExposure.Result.state] using own

/-- Every projection-job outcome retains the original annotation predicate. -/
theorem projections_heap (annotation : Guard → Prop) (projectionFuel readFuel : Nat)
    (jobs : List (Job Symbol Formula)) (before : Physical Symbol Formula)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (inputs : SourceCurrentConjunctionCompletionReads.Inputs before.heap jobs)
    (heap : Heap annotation before.heap) :
    HeapOutcome annotation (projections projectionFuel readFuel jobs before) := by
  induction jobs generalizing before with
  | nil => exact heap
  | cons job jobs ih =>
      obtain ⟨forest, path⟩ := job
      have initial := inputs _ List.mem_cons_self
      have own := SourceEqualityAnnotationProjectionOutcome.forest_heap annotation projectionFuel readFuel
        (path.map Int.ofNat) forest before.heap semantic initial.1 initial.2 heap
      cases observed : SourceEqualityProjectionWorker.forest projectionFuel readFuel
          (path.map Int.ofNat) forest before.heap with
      | done value middle =>
          have actual := SourceEqualityProjectionWorkerSound.forest_graph _ _ _ _ _ _ _ observed
          have checked := SourceEqualityProjectionCosts.forest_effects actual semantic costs initial.1
          have middleHeap : Heap annotation middle := by
            simpa only [observed, SourceEqualityAnnotationProjectionOutcome.ResultHeap] using own
          simp only [projections, observed]
          exact map_heap annotation _ _ (ih ⟨middle, before.equality⟩ checked.2.1 checked.2.2.1
            (SourceCurrentConjunctionCompletionReads.Inputs.keeps
              (fun job member => inputs job (List.mem_cons_of_mem _ member)) checked.1) middleHeap)
      | pending key middle =>
          simpa only [projections, observed, HeapOutcome, Outcome.state,
            SourceEqualityAnnotationProjectionOutcome.ResultHeap] using own
      | unresolved name middle =>
          simpa only [projections, observed, HeapOutcome, Outcome.state,
            SourceEqualityAnnotationProjectionOutcome.ResultHeap] using own
      | exhausted limit middle =>
          simpa only [projections, observed, HeapOutcome, Outcome.state,
            SourceEqualityAnnotationProjectionOutcome.ResultHeap] using own

/-- Every class sequence retains annotations at its actual returned heap. -/
theorem classes_heap (annotation : Guard → Prop) (projectionFuel readFuel : Nat)
    (forests : List (List (Value Symbol Guard))) (constraints : EqualityNormalize.Constraints)
    (before : Physical Symbol Formula) (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (available : ∀ forest ∈ forests, Values before.heap forest)
    (closed : ∀ forest ∈ forests, ClosedValues forest) (heap : Heap annotation before.heap) :
    HeapOutcome annotation (classes projectionFuel readFuel forests constraints before) := by
  induction constraints generalizing before with
  | nil => exact heap
  | cons paths constraints ih =>
      have inputs := SourceCurrentConjunctionCompletionReads.jobs_inputs before.heap forests paths available closed
      have first := projections_heap annotation projectionFuel readFuel _ before semantic costs inputs heap
      simp only [classes]
      apply bind_heap annotation _ _ first
      intro projected middle observed
      have actual := (SourceCurrentConjunctionRowsWorkerActual.projections_graph observed).1
      have checked := SourceCurrentConjunctionCompletionReads.Projections.verified annotation
        actual semantic costs heap inputs
      exact map_heap annotation _ _ (ih middle checked.1.semantic checked.1.costs
        (fun forest member value included => checked.1.keeps.available value
          (available forest member value included)) checked.1.annotations)

/-- Literal child columns do not change the heap returned by class projection. -/
theorem requirements_heap (annotation : Guard → Prop) (projectionFuel readFuel : Nat)
    (edges : List (EdgeValue Symbol Guard)) (constraints : EqualityNormalize.Constraints)
    (before : Physical Symbol Formula) (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (available : ∀ edge ∈ edges, Values before.heap edge.children)
    (closed : ClosedEdges edges) (heap : Heap annotation before.heap) :
    HeapOutcome annotation (requirements projectionFuel readFuel edges constraints before) := by
  have own := classes_heap annotation projectionFuel readFuel (edges.map EdgeValue.children) constraints
    before semantic costs
    (fun forest member => by
      obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
      exact available edge edgeMember)
    (fun forest member => by
      obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp member
      exact closed edge edgeMember) heap
  exact map_heap annotation _ _ own

/-- Equality-fold failure retains the graph heap before requirement projection. -/
theorem tuple_heap (annotation : Guard → Prop) (projectionFuel readFuel : Nat)
    (edges : List (EdgeValue Symbol Guard)) (before : Physical Symbol Formula)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (resident : Edges before.heap edges) (closed : ClosedEdges edges)
    (heap : Heap annotation before.heap) :
    HeapOutcome annotation (tuple projectionFuel readFuel edges before) := by
  unfold tuple
  dsimp only
  split
  · exact heap
  · exact heap
  · rename_i result folded
    split
    · exact heap
    · rename_i constraints observed
      exact map_heap annotation _ _ (requirements_heap annotation projectionFuel readFuel edges constraints
        _ semantic costs
        (fun edge member child included => semantic.ready.semantic.1.normal.facts.cached.edges
          edge.entry.key edge (resident edge member) child included) closed heap)

/-- Every actual tuple prefix supplies the next tuple at its returned physical state. -/
theorem tuples_heap (annotation : Guard → Prop) (projectionFuel readFuel : Nat)
    (tuples : List (List (EdgeValue Symbol Guard))) (before : Physical Symbol Formula)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple)
    (same : ∀ tuple ∈ tuples, SourceCurrentConjunctionRequirements.SameArity tuple)
    (heap : Heap annotation before.heap) :
    HeapOutcome annotation (SourceCurrentConjunctionRowsWorker.tuples projectionFuel readFuel tuples before) := by
  induction tuples generalizing before with
  | nil => exact heap
  | cons edges remaining ih =>
      have first := tuple_heap annotation projectionFuel readFuel edges before ready.semantic ready.costs
        (resident edges List.mem_cons_self) (closed edges List.mem_cons_self) heap
      simp only [SourceCurrentConjunctionRowsWorker.tuples]
      apply bind_heap annotation _ _ first
      intro row middle observed
      have actual := SourceCurrentConjunctionRowsWorkerActual.tuple_graph (same edges List.mem_cons_self) observed
      have checked := SourceCurrentConjunctionRowsAllocation.Tuple.verified actual ready
        (resident edges List.mem_cons_self) (closed edges List.mem_cons_self)
      have middleHeap : Heap annotation middle.heap := by
        simpa only [observed, HeapOutcome, Outcome.state] using first
      exact map_heap annotation _ _ (ih middle checked.1.ready
        (fun tuple member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap
          checked.1.keeps.growth edge (resident tuple (List.mem_cons_of_mem edges member) edge included))
        (fun tuple member => closed tuple (List.mem_cons_of_mem edges member))
        (fun tuple member => same tuple (List.mem_cons_of_mem edges member)) middleHeap)

/-- Every raw row outcome retains the same arbitrary annotation predicate. -/
theorem rows_heap [DecidableEq Symbol] (annotation : Guard → Prop) (projectionFuel readFuel : Nat)
    (nodes : List (Value Symbol Guard)) (before : Physical Symbol Formula)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (heap : Heap annotation before.heap) :
    HeapOutcome annotation (rows projectionFuel readFuel nodes before) := by
  have first := exposures_heap annotation readFuel nodes before ready.semantic ready.costs available closed heap
  unfold rows
  apply bind_heap annotation _ _ first
  intro edges middle observed
  have actual := SourceCurrentConjunctionRowsWorkerActual.exposures_graph observed
  have checked := SourceCurrentConjunctionCompletionReads.Exposures.verified
    (SourceCurrentConjunctionEquality.FieldAvailable before.equality) actual.1
    ready.semantic ready.costs ready.fields available closed
  have middleReady : SourceCurrentConjunctionRowsAllocation.Ready middle :=
    ⟨checked.1.semantic, checked.1.costs, by simpa only [actual.2] using ready.valid,
      by simpa only [SourceCurrentConjunctionEquality.Fields, actual.2] using checked.1.annotations⟩
  have facts := SourceCurrentConjunctionTuples.tuples_verified
    (SourceCurrentConjunctionEquality.FieldAvailable before.equality) actual.1
    ready.semantic ready.costs ready.fields available closed
  have middleHeap : Heap annotation middle.heap := by
    simpa only [observed, HeapOutcome, Outcome.state] using first
  exact tuples_heap annotation projectionFuel readFuel _ middle middleReady
    (fun tuple member => (facts tuple member).2.1)
    (fun tuple member => (facts tuple member).2.2)
    (fun tuple member => SourceCurrentConjunctionRowsAllocation.matching_arity tuple
      (SourceCurrentConjunctionTuples.tuples_matching edges tuple member)) middleHeap

end MicroCFTA.SourceCurrentConjunctionRowsAnnotationOutcome
