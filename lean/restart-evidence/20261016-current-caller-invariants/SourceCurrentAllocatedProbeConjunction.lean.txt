import MicroCFTA.SourceCurrentAllocatedProbeExposure
import MicroCFTA.SourceCurrentConjunctionMemo

/-!
# Filtered probes through current conjunction decisions

Actual row exposure and class projection retain the probe heap. Tuple
allocation changes equality operations without changing constructor records.
The worklist proof follows only admitted rows and reached pending inputs.
Open inputs and completed memo hits retain the same constructor heap.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeConjunction
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open InternedFreshOrdinaryProbeHeap (Heap)
open SourceCurrentConjunctionCompletionReads
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "TrueHeap" => SourceEqualityAnnotationHeap.Heap (fun _ => True)

private theorem true_heap (state : State Symbol Guard) : TrueHeap state := by
  intro key edge present
  trivial

/-- Actual ordered exposures preserve probes without a whole-input closedness premise. -/
theorem exposures_heap [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (List (EdgeValue Symbol Guard))} (actual : Exposures values before rows after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (probes : Heap before) : Heap after := by
  induction actual with
  | nil => exact probes
  | cons first rest ih =>
      have own := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      exact ih own.2.1 own.2.2.1
        (fun value member => own.1.available value (available value (List.mem_cons_of_mem _ member)))
        (SourceCurrentAllocatedProbeExposure.read_heap first semantic (available _ List.mem_cons_self) probes)

/-- Actual projection jobs retain the exact returned probe heaps in their stored order. -/
theorem projections_heap [DecidableEq (EdgeKey Symbol Guard)]
    {jobs : List (Job Symbol Guard)} {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : Projections jobs before values after) (semantic : SemanticReady before)
    (costs : CostHeap before) (inputs : Inputs before jobs) (probes : Heap before) : Heap after := by
  induction actual with
  | nil => exact probes
  | cons first rest ih =>
      have selected := inputs _ List.mem_cons_self
      have own := SourceEqualityProjectionCosts.forest_effects first semantic costs selected.1
      exact ih own.2.1 own.2.2.1
        (Inputs.keeps (fun job member => inputs job (List.mem_cons_of_mem _ member)) own.1)
        (SourceCurrentAllocatedProbeExposure.forest_heap first semantic costs selected.1 probes)

/-- Each actual class uses the original forests at its current constructor heap. -/
theorem classes_heap [DecidableEq (EdgeKey Symbol Guard)]
    {forests : List (List (Value Symbol Guard))} {classes : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : SourceCurrentConjunctionRequirements.ClassRequirements forests classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : SourceCurrentConjunctionRequirements.RowsReady before forests) (probes : Heap before) : Heap after := by
  induction actual with
  | nil => exact probes
  | @cons paths before projected middle classes requirements after first rest ih =>
      have jobs := jobs_inputs before forests paths (fun forest member => (inputs forest member).1)
        (fun forest member => (inputs forest member).2)
      have own := first.verified (fun _ => True) semantic costs (true_heap _) jobs
      exact ih own.1.semantic own.1.costs
        (fun forest member => ⟨fun value included => own.1.keeps.available value ((inputs forest member).1 value included),
          (inputs forest member).2⟩)
        (projections_heap first semantic costs jobs probes)

/-- Column construction has no heap effect beyond its actual class projections. -/
theorem requirements_heap [DecidableEq (EdgeKey Symbol Guard)]
    {tuple : List (EdgeValue Symbol Guard)} {classes : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : SourceCurrentConjunctionRequirements.Requirements tuple classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) (probes : Heap before) : Heap after := by
  cases actual with
  | run _ actual =>
      exact classes_heap actual semantic costs
        (SourceCurrentConjunctionRequirements.tuple_inputs tuple before semantic resident closed) probes

open SourceCurrentConjunctionRowsAllocation (Ready Tuple Tuples Rows)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula

/-- Contradiction stops before projections; the live branch uses its actual requirements. -/
theorem tuple_heap [DecidableEq (EdgeKey Symbol Guard)]
    {tuple : List (EdgeValue Symbol Guard)} {before after : Physical}
    {rows : Option (List (List (Value Symbol Guard)))} (actual : Tuple tuple before rows after)
    (ready : Ready before) (resident : Edges before.heap tuple) (closed : ClosedEdges tuple)
    (probes : Heap before.heap) : Heap after.heap := by
  cases actual with
  | contradiction => exact probes
  | live _ _ requirements => exact requirements_heap requirements ready.semantic ready.costs resident closed probes

/-- Ordered tuples retain probes at each literal returned allocation state. -/
theorem tuples_heap [DecidableEq (EdgeKey Symbol Guard)]
    {tuples : List (List (EdgeValue Symbol Guard))} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Tuples tuples before rows after)
    (ready : Ready before) (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple) (probes : Heap before.heap) : Heap after.heap := by
  induction actual with
  | nil => exact probes
  | skip first rest ih | keep first rest ih =>
      have own := first.verified ready (resident _ List.mem_cons_self) (closed _ List.mem_cons_self)
      exact ih own.1.ready
        (fun tuple member edge included => InternedEdgeResidency.edge_grows _ _ own.1.keeps.growth edge
          (resident tuple (List.mem_cons_of_mem _ member) edge included))
        (fun tuple member => closed tuple (List.mem_cons_of_mem _ member))
        (tuple_heap first ready (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) probes)

/-- Actual admitted rows preserve probes through exposures and equality allocation. -/
theorem rows_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {nodes : List (Value Symbol Guard)} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Rows nodes before rows after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (probes : Heap before.heap) : Heap after.heap := by
  cases actual with
  | run reads tuples =>
      rename_i edges heap
      have own := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      have middle : Ready (⟨heap, before.equality⟩ : Physical) :=
        ⟨own.1.semantic, own.1.costs, ready.valid, own.1.annotations⟩
      exact tuples_heap tuples middle
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality) reads ready.semantic ready.costs
          ready.fields available closed tuple member).2.1)
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified
          (SourceCurrentConjunctionEquality.FieldAvailable before.equality) reads ready.semantic ready.costs
          ready.fields available closed tuple member).2.2)
        (exposures_heap reads ready.semantic ready.costs available probes)

/-- Actual worklist admissions derive all reached probe heaps from the initial one. -/
theorem run_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {budget : Nat} {table final : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard))}
    {pending : List (List (Value Symbol Guard))} {before after : Physical}
    (actual : SourceCurrentConjunctionWorklist.Run budget table pending before final after)
    (ready : Ready before) (available : SourceCurrentConjunctionWorklist.PendingReady before pending)
    (probes : Heap before.heap) : Heap after.heap := by
  induction actual with
  | done => exact probes
  | empty impossible rest ih | skip nonempty skipped rest ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) probes
  | admit nonempty fresh rows rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)
        SourceCurrentConjunctionWorklist.closed _ _ _ fresh
      have inputs := available _ List.mem_cons_self
      have closed := SourceCurrentConjunctionWorklist.closed_values _ admitted.2.1
      have own := SourceCurrentConjunctionRowsSoundness.rows_verified rows ready inputs closed
      apply ih own.1.ready
      · intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2 row rowIn requirement requirementIn).1
        · exact SourceCurrentConjunctionWorklist.pending_keeps own.1.keeps
            (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier
      · exact rows_heap rows ready inputs closed probes

/-- Both current decision branches retain probes; Boolean grow adds no constructor work. -/
theorem decision_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {start : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionDecision.Decision budget start before answer after)
    (ready : Ready before) (available : Available before.heap start) (probes : Heap before.heap) : Heap after.heap := by
  cases actual with
  | open_input => exact probes
  | closed _ explored _ =>
      exact run_heap explored ready
        (by intro nodes member value included; cases List.mem_singleton.mp member; cases List.mem_singleton.mp included; exact available) probes


/-- A current memo hit skips the body; a miss retains the actual decision probes. -/
theorem call_heap [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    [DecidableEq (Value (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    {budget : Nat} {memo saved : SourceCurrentEmptinessMemo.Memo}
    {query : Value (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula)}
    {before after : SourceCurrentConjunctionRowsAllocation.State (SourceObservations.Label FullSyntax.Formula) FullSyntax.Formula}
    {answer : Bool} (actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved)
    (ready : Ready before) (available : Available before.heap query) (probes : Heap before.heap) : Heap after.heap := by
  cases actual with
  | hit => exact probes
  | miss _ decision => exact decision_heap decision ready available probes

end MicroCFTA.SourceCurrentAllocatedProbeConjunction
