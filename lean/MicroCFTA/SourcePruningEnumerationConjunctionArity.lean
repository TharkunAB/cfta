import MicroCFTA.SourceCurrentConjunctionMemo
import MicroCFTA.SourcePruningEnumerationProjectionArity

/-!
# Arity through actual conjunction allocation

Each actual read and projection retains the whole edge-record invariant.
Tuple and worklist steps use their actual returned physical states.
Memo hits retain the input state. Misses use the actual decision receipt.
-/
namespace MicroCFTA.SourcePruningEnumerationConjunctionArity
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourcePruningEnumerationArityOrigins (Heap)
namespace Reads
export SourceCurrentConjunctionCompletionReads (Exposures Projections Inputs jobs)
end Reads
namespace Req
export SourceCurrentConjunctionRequirements (ClassRequirements Requirements RowsReady)
end Req
namespace Allocation
export SourceCurrentConjunctionRowsAllocation (Ready Tuple Tuples Rows)
end Allocation
section Generic
variable {Symbol : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Each actual exposure keeps arity at the exact heap passed to its suffix. -/
theorem exposures_heap
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (List (EdgeValue Symbol Guard))}
    (actual : Reads.Exposures values before edges after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (heap : Heap before) : Heap after := by
  induction actual with
  | nil => exact heap
  | @cons value before edges middle values more after first rest ih =>
      have own := SourceEqualityProjectionCosts.read_effects first semantic costs
        (available _ List.mem_cons_self)
      have current := SourcePruningEnumerationProbeExposureArity.read_heap first
        semantic.ready.semantic.1.normal.facts (available _ List.mem_cons_self) heap
      exact ih own.2.1 own.2.2.1
        (fun child member => own.1.available child (available child (List.mem_cons_of_mem _ member))) current

/-- Actual projection jobs keep the heap invariant in their literal order. -/
theorem projections_heap
    {jobs : List (SourceCurrentConjunctionCompletionReads.Job Symbol Guard)}
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : Reads.Projections jobs before values after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : Reads.Inputs before jobs) (heap : Heap before) : Heap after := by
  induction actual with
  | nil => exact heap
  | @cons children path before value middle remaining values after first rest ih =>
      have ownInputs := inputs _ List.mem_cons_self
      have own := SourceEqualityProjectionCosts.forest_effects first semantic costs ownInputs.1
      have current := SourcePruningEnumerationProjectionArity.forest_heap first semantic costs ownInputs.1 heap
      exact ih own.2.1 own.2.2.1
        (SourceCurrentConjunctionCompletionReads.Inputs.keeps
          (fun job member => inputs job (List.mem_cons_of_mem _ member)) own.1) current

/-- Actual class requirements derive arity at every returned projection heap. -/
theorem classRequirements_heap
    {forests : List (List (Value Symbol Guard))} {classes : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Req.ClassRequirements forests classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : Req.RowsReady before forests) (heap : Heap before) : Heap after := by
  induction actual with
  | nil => exact heap
  | @cons paths before projected middle classes requirements after first rest ih =>
      have jobs := SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
        (fun forest member => (inputs forest member).1)
        (fun forest member => (inputs forest member).2)
      have own := first.verified (fun _ => True) semantic costs
        (by intro key edge present; trivial) jobs
      have current := projections_heap first semantic costs jobs heap
      exact ih own.1.semantic own.1.costs
        (fun forest member =>
          ⟨fun child included => own.1.keeps.available child ((inputs forest member).1 child included),
            (inputs forest member).2⟩) current

/-- Original resident tuple edges derive the inputs for actual class projection. -/
theorem requirements_heap
    {tuple : List (EdgeValue Symbol Guard)} {classes : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Req.Requirements tuple classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) (heap : Heap before) : Heap after := by
  cases actual with
  | run _ classes =>
      exact classRequirements_heap classes semantic costs
        (SourceCurrentConjunctionRequirements.tuple_inputs tuple before semantic resident closed) heap

/-- Equality contradiction and live tuple allocation both retain whole-record arity. -/
theorem tuple_heap
    {tuple : List (EdgeValue Symbol Guard)} {before after : Physical}
    {rows : Option (List (List (Value Symbol Guard)))}
    (actual : Allocation.Tuple tuple before rows after) (ready : Allocation.Ready before)
    (resident : Edges before.heap tuple) (closed : ClosedEdges tuple)
    (heap : Heap before.heap) : Heap after.heap := by
  cases actual with
  | contradiction _ _ => exact heap
  | live _ _ requirements =>
      exact requirements_heap requirements ready.semantic ready.costs resident closed heap

/-- Every actual tuple advances its exact physical endpoint before the next tuple. -/
theorem tuples_heap
    {tuples : List (List (EdgeValue Symbol Guard))} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))}
    (actual : Allocation.Tuples tuples before rows after) (ready : Allocation.Ready before)
    (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple) (heap : Heap before.heap) : Heap after.heap := by
  induction actual with
  | nil => exact heap
  | skip first rest ih | keep first rest ih =>
      have own := first.verified ready (resident _ List.mem_cons_self) (closed _ List.mem_cons_self)
      have current := tuple_heap first ready (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) heap
      exact ih own.1.ready
        (fun chosen member edge present => InternedEdgeResidency.edge_grows _ _ own.1.keeps.growth edge
          (resident chosen (List.mem_cons_of_mem _ member) edge present))
        (fun chosen member => closed chosen (List.mem_cons_of_mem _ member)) current

variable [DecidableEq Symbol]

/-- Actual exposures and tuple allocations preserve arity from the original physical input. -/
theorem rows_heap
    {nodes : List (Value Symbol Guard)} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))}
    (actual : Allocation.Rows nodes before rows after) (ready : Allocation.Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (heap : Heap before.heap) : Heap after.heap := by
  cases actual with
  | run reads tuples =>
      have own := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      have current := exposures_heap reads ready.semantic ready.costs available heap
      apply tuples_heap tuples ⟨own.1.semantic, own.1.costs, ready.valid, own.1.annotations⟩
      · intro tuple member
        exact (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available closed tuple member).2.1
      · intro tuple member
        exact (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
          reads ready.semantic ready.costs ready.fields available closed tuple member).2.2
      · exact current

/-- The actual dynamic worklist derives arity without a final-heap supplier. -/
theorem run_heap
    {budget : Nat}
    {table final : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard))}
    {pending : List (List (Value Symbol Guard))} {before after : Physical}
    (actual : SourceCurrentConjunctionWorklist.Run budget table pending before final after)
    (ready : Allocation.Ready before)
    (available : SourceCurrentConjunctionWorklist.PendingReady before pending)
    (heap : Heap before.heap) : Heap after.heap := by
  induction actual with
  | done => exact heap
  | empty _ _ ih | skip _ _ _ ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) heap
  | @admit budget table nodes before requirements middle pending final after nonempty fresh rows rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have own := SourceCurrentConjunctionRowsSoundness.rows_verified rows ready inputs noFree
      have current := rows_heap rows ready inputs noFree heap
      have nextPending : SourceCurrentConjunctionWorklist.PendingReady middle
          (requirements.flatten ++ pending) := by
        intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2 row rowIn requirement requirementIn).1
        · exact SourceCurrentConjunctionWorklist.pending_keeps own.1.keeps
            (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier
      exact ih own.1.ready nextPending current

variable [DecidableEq (Value Symbol Guard)]

/-- Both actual decision branches preserve arity at their exact physical endpoint. -/
theorem decision_heap
    {budget : Nat} {query : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionDecision.Decision budget query before answer after)
    (ready : Allocation.Ready before) (available : Available before.heap query)
    (heap : Heap before.heap) : Heap after.heap := by
  cases actual with
  | open_input _ => exact heap
  | closed _ explored _ =>
      apply run_heap explored ready
      · intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available
      · exact heap
end Generic

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- An actual conjunction memo hit or miss retains arity without a memo-correctness premise. -/
theorem call_heap
    {budget : Nat} {query : Value Symbol Guard} {before after : Physical} {answer : Bool}
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Available before.heap query) (heap : Heap before.heap) : Heap after.heap := by
  cases actual with
  | hit _ => exact heap
  | miss _ decision => exact decision_heap decision ready available heap

end MicroCFTA.SourcePruningEnumerationConjunctionArity
