import MicroCFTA.SourceEqualityAnnotationProjection
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceEqualityRequiredWorkerSound

/-!
# Annotation heaps through actual projection outcomes

Every result retains the input annotation predicate in its reached heap.
The initial semantic and residency gates remain explicit.
-/
namespace MicroCFTA.SourceEqualityAnnotationProjectionOutcome
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredWorker (Result)
open SourceEqualityAnnotationHeap (Heap)

/-- Every returned state retains the annotation heap, including blocked states. -/
def ResultHeap (annotation : Guard → Prop) : Result Symbol Guard A → Prop
  | .done _ after | .pending _ after | .unresolved _ after | .exhausted _ after =>
      Heap annotation after

private theorem append_heap (annotation : Guard → Prop)
    (earlier : List (EdgeValue Symbol Guard))
    (result : Result Symbol Guard (List (EdgeValue Symbol Guard)))
    (heap : ResultHeap annotation result) :
    ResultHeap annotation (result.bind fun more after => .done (earlier ++ more) after) := by
  cases result <;> exact heap

/-- Ordinary node construction does not require a new guard annotation. -/
theorem makeNode_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (heap : Heap annotation before) :
    ResultHeap annotation (SourceEqualityRequiredWorker.work (makeNode edges) before) := by
  change Heap annotation (InternedConstructorTemplates.run (makeNode edges) before).2
  exact SourceEqualityAnnotationHeap.run annotation _
    (SourceEqualityAnnotationHeap.makeNode annotation edges) before heap

/-- Actual head exposure preserves the heap at every returned outcome. -/
theorem head_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (readFuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value)
    (closed : value.free = []) (heap : Heap annotation before) :
    ResultHeap annotation (SourceEqualityRequiredWorker.head readFuel value before) := by
  have retained := SourceEqualityAnnotationExposure.nodeEdges_heap annotation readFuel value before
    semantic.ready.semantic semantic.ready.covered heap available closed
  cases observed : MergedFreshOrdinaryExposure.nodeEdges readFuel value before with
  | done edges after =>
      have afterHeap : Heap annotation after := by
        simpa only [observed, MergedSourceExposure.Result.state] using retained
      simpa only [SourceEqualityRequiredWorker.head, observed] using
        makeNode_heap annotation edges after afterHeap
  | pending key after =>
      simpa only [SourceEqualityRequiredWorker.head, observed, ResultHeap,
        MergedSourceExposure.Result.state] using retained
  | unresolved name after =>
      simpa only [SourceEqualityRequiredWorker.head, observed, ResultHeap,
        MergedSourceExposure.Result.state] using retained
  | exhausted after =>
      simpa only [SourceEqualityRequiredWorker.head, observed, ResultHeap,
        MergedSourceExposure.Result.state] using retained

/-- The literal ordered row reader preserves every retained result state. -/
theorem readAll_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (readFuel : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values)
    (closed : ClosedValues values) (heap : Heap annotation before) :
    ResultHeap annotation (SourceEqualityProjectionWorker.readAll readFuel values before) := by
  induction values generalizing before with
  | nil => exact heap
  | cons value values ih =>
      have firstAvailable := available value List.mem_cons_self
      have firstClosed := closed value List.mem_cons_self
      have retained := SourceEqualityAnnotationExposure.nodeEdges_heap annotation readFuel value before
        semantic.ready.semantic semantic.ready.covered heap firstAvailable firstClosed
      cases observed : MergedFreshOrdinaryExposure.nodeEdges readFuel value before with
      | done edges middle =>
          have trace : SourceEqualityProjectionRead.Read value before edges middle := .done readFuel observed
          have checked := trace.verified semantic firstAvailable firstClosed
          have middleHeap : Heap annotation middle := by
            simpa only [observed, MergedSourceExposure.Result.state] using retained
          have restAvailable : Values middle values := fun child member =>
            checked.1.available child (available child (List.mem_cons_of_mem _ member))
          have restClosed : ClosedValues values := fun child member =>
            closed child (List.mem_cons_of_mem _ member)
          have rest := ih middle checked.2.1 restAvailable restClosed middleHeap
          simpa only [SourceEqualityProjectionWorker.readAll, observed] using
            append_heap annotation edges _ rest
      | pending key after =>
          simpa only [SourceEqualityProjectionWorker.readAll, observed, ResultHeap,
            MergedSourceExposure.Result.state] using retained
      | unresolved name after =>
          simpa only [SourceEqualityProjectionWorker.readAll, observed, ResultHeap,
            MergedSourceExposure.Result.state] using retained
      | exhausted after =>
          simpa only [SourceEqualityProjectionWorker.readAll, observed, ResultHeap,
            MergedSourceExposure.Result.state] using retained

/-- The actual union branch preserves the heap on success or a retained block. -/
theorem union_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (readFuel : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values)
    (closed : ClosedValues values) (heap : Heap annotation before) :
    ResultHeap annotation (SourceEqualityProjectionWorker.union readFuel values before) := by
  have retained := readAll_heap annotation readFuel values before semantic available closed heap
  cases observed : SourceEqualityProjectionWorker.readAll readFuel values before with
  | done edges after =>
      have afterHeap : Heap annotation after := by simpa only [observed, ResultHeap] using retained
      simpa only [SourceEqualityProjectionWorker.union, observed, Result.bind] using
        makeNode_heap annotation edges after afterHeap
  | pending key after =>
      simpa only [SourceEqualityProjectionWorker.union, observed, Result.bind, ResultHeap] using retained
  | unresolved name after =>
      simpa only [SourceEqualityProjectionWorker.union, observed, Result.bind, ResultHeap] using retained
  | exhausted limit after =>
      simpa only [SourceEqualityProjectionWorker.union, observed, Result.bind, ResultHeap] using retained

/-- Forest root projection is the same actual union branch for all worker bounds. -/
theorem forest_root_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values)
    (closed : ClosedValues values) (heap : Heap annotation before) :
    ResultHeap annotation (SourceEqualityProjectionWorker.forest fuel readFuel [] values before) := by
  exact union_heap annotation readFuel values before semantic available closed heap

open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceEqualityProjectionGraph (select select_member)

private theorem cons_heap (annotation : Guard → Prop) (value : Value Symbol Guard)
    (result : Result Symbol Guard (List (Value Symbol Guard)))
    (heap : ResultHeap annotation result) :
    ResultHeap annotation (result.bind fun values after => .done (value :: values) after) := by
  cases result <;> exact heap

private theorem rows_project_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (path : List Int)
    (smaller : ∀ (value : Value Symbol Guard) (before : State Symbol Guard),
      SemanticReady before → Available before value → value.free = [] →
      Heap annotation before → ResultHeap annotation (SourceEqualityProjectionWorker.project fuel readFuel path value before))
    (index : Int) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (resident : Edges before edges)
    (closed : ClosedEdges edges) (heap : Heap annotation before) :
    ResultHeap annotation (SourceEqualityProjectionWorker.rows
      (SourceEqualityProjectionWorker.project fuel readFuel path) index edges before) := by
  induction edges generalizing before with
  | nil => exact heap
  | cons edge edges ih =>
      cases found : select edge.children index with
      | none =>
          simpa only [SourceEqualityProjectionWorker.rows, found] using
            ih before semantic
              (fun row member => resident row (List.mem_cons_of_mem _ member))
              (fun row member => closed row (List.mem_cons_of_mem _ member)) heap
      | some child =>
          have member := select_member found
          have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges
            edge.entry.key edge (resident edge List.mem_cons_self) child member
          have childClosed := closed edge List.mem_cons_self child member
          have retained := smaller child before semantic childAvailable childClosed heap
          cases observed : SourceEqualityProjectionWorker.project fuel readFuel path child before with
          | done value middle =>
              have middleHeap : Heap annotation middle := by
                simpa only [observed, ResultHeap] using retained
              have trace := SourceEqualityProjectionWorkerSound.project_graph
                fuel readFuel path child before value middle observed
              have checked := SourceEqualityProjectionEffects.node trace semantic childAvailable childClosed
              have restResident : Edges middle edges := fun row member =>
                InternedEdgeResidency.edge_grows before middle checked.1.growth row
                  (resident row (List.mem_cons_of_mem _ member))
              have restClosed : ClosedEdges edges := fun row member =>
                closed row (List.mem_cons_of_mem _ member)
              have rest := ih middle checked.2.1 restResident restClosed middleHeap
              simpa only [SourceEqualityProjectionWorker.rows, found, observed, Result.bind] using
                cons_heap annotation value _ rest
          | pending key after =>
              simpa only [SourceEqualityProjectionWorker.rows, found, observed, Result.bind, ResultHeap] using retained
          | unresolved name after =>
              simpa only [SourceEqualityProjectionWorker.rows, found, observed, Result.bind, ResultHeap] using retained
          | exhausted limit after =>
              simpa only [SourceEqualityProjectionWorker.rows, found, observed, Result.bind, ResultHeap] using retained

private theorem head_project_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (path : List Int)
    (smaller : ∀ (value : Value Symbol Guard) (before : State Symbol Guard),
      SemanticReady before → Available before value → value.free = [] →
      Heap annotation before → ResultHeap annotation (SourceEqualityProjectionWorker.project fuel readFuel path value before))
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value)
    (closed : value.free = []) (heap : Heap annotation before) :
    ResultHeap annotation ((SourceEqualityRequiredWorker.head readFuel value before).bind
      fun exposed middle => SourceEqualityProjectionWorker.project fuel readFuel path exposed middle) := by
  have retained := head_heap annotation readFuel value before semantic available closed heap
  cases observed : SourceEqualityRequiredWorker.head readFuel value before with
  | done exposed middle =>
      have middleHeap : Heap annotation middle := by
        simpa only [observed, ResultHeap] using retained
      have trace := SourceEqualityRequiredWorkerSound.head_graph readFuel value before exposed middle observed
      have checked := trace.verified semantic.ready available closed
      have middleSemantic := SourceEqualityRequiredSemanticCache.head trace semantic available closed
      simpa only [observed, Result.bind] using
        smaller exposed middle middleSemantic checked.2.1 checked.2.2.1 middleHeap
  | pending key after =>
      simpa only [observed, Result.bind, ResultHeap] using retained
  | unresolved name after =>
      simpa only [observed, Result.bind, ResultHeap] using retained
  | exhausted limit after =>
      simpa only [observed, Result.bind, ResultHeap] using retained

/-- Actual path projection preserves every returned heap, for arbitrary proof bounds. -/
theorem project_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (path : List Int) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value)
    (closed : value.free = []) (heap : Heap annotation before) :
    ResultHeap annotation (SourceEqualityProjectionWorker.project fuel readFuel path value before) := by
  induction fuel generalizing path value before with
  | zero => exact heap
  | succ fuel ih =>
      cases path with
      | nil => exact heap
      | cons index path =>
          cases value with
          | empty => exact heap
          | reference name => exact heap
          | node entry edges depth free =>
              have read : SourceEqualityProjectionRead.Read (.node entry edges depth free) before edges before :=
                .done readFuel rfl
              have inputs := read.verified semantic available closed
              have retained := rows_project_heap annotation fuel readFuel path (ih path)
                index edges before semantic inputs.2.2.1 inputs.2.2.2 heap
              cases observed : SourceEqualityProjectionWorker.rows
                  (SourceEqualityProjectionWorker.project fuel readFuel path) index edges before with
              | done values middle =>
                  have middleHeap : Heap annotation middle := by
                    simpa only [observed, ResultHeap] using retained
                  have trace := SourceEqualityProjectionWorkerSound.rows_graph
                    (SourceEqualityProjectionWorker.project fuel readFuel path) path
                    (fun child state result after done =>
                      SourceEqualityProjectionWorkerSound.project_graph fuel readFuel path child state result after done)
                    index edges before values middle observed
                  have checked := SourceEqualityProjectionEffects.rows trace semantic inputs.2.2.1 inputs.2.2.2
                  simpa only [SourceEqualityProjectionWorker.project, observed, Result.bind] using
                    union_heap annotation readFuel values middle checked.2.1 checked.2.2.1 checked.2.2.2 middleHeap
              | pending key after =>
                  simpa only [SourceEqualityProjectionWorker.project, observed, Result.bind, ResultHeap] using retained
              | unresolved name after =>
                  simpa only [SourceEqualityProjectionWorker.project, observed, Result.bind, ResultHeap] using retained
              | exhausted limit after =>
                  simpa only [SourceEqualityProjectionWorker.project, observed, Result.bind, ResultHeap] using retained
          | mu entry body depth ordinary =>
              simpa only [SourceEqualityProjectionWorker.project] using
                head_project_heap annotation fuel readFuel (index :: path) (ih (index :: path))
                  (.mu entry body depth ordinary) before semantic available closed heap
          | union entry members depth free =>
              simpa only [SourceEqualityProjectionWorker.project] using
                head_project_heap annotation fuel readFuel (index :: path) (ih (index :: path))
                  (.union entry members depth free) before semantic available closed heap

/-- Every forest branch preserves the retained heap on success or a block. -/
theorem forest_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (path : List Int) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values)
    (closed : ClosedValues values) (heap : Heap annotation before) :
    ResultHeap annotation (SourceEqualityProjectionWorker.forest fuel readFuel path values before) := by
  cases path with
  | nil => exact union_heap annotation readFuel values before semantic available closed heap
  | cons index path =>
      cases found : select values index with
      | none => simpa only [SourceEqualityProjectionWorker.forest, found, ResultHeap] using heap
      | some value =>
          have member := select_member found
          simpa only [SourceEqualityProjectionWorker.forest, found] using
            project_heap annotation fuel readFuel path value before semantic
              (available value member) (closed value member) heap

end MicroCFTA.SourceEqualityAnnotationProjectionOutcome
