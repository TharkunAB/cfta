import MicroCFTA.SourceCurrentConjunctionWorklist
import MicroCFTA.SourceRecursiveIntersectionSourceProfile

/-!
# Original physical guards through actual conjunction exploration

Successful initial edge reads give a finite raw guard carrier.
Requirement projections reuse these guards. Equality-cache field readiness
remains a separate invariant. Each graph retains its exact returned states.
-/
namespace MicroCFTA.SourceCurrentConjunctionGuardUniverse
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConjunctionRowsAllocation (Ready Effects Tuple Tuples Rows RowsReady)
open SourceCurrentConjunctionWorklist (Run PendingReady TableReady)
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap

/-- Successful initial edge payload reads supply the raw guard carrier. -/
def guards (source : State Symbol Guard) : List Guard :=
  (SourceRecursiveIntersectionSourceProfile.edgePayloads source).map (fun edge => edge.entry.key.constraint)

/-- Coherent actual initial edge records establish their own finite carrier. -/
theorem initial (source : State Symbol Guard) (facts : Facts source) :
    AnnotationHeap (fun guard => guard ∈ guards source) source := by
  intro key edge found
  have same := (facts.coherent.edges key edge found).2.1
  have resident : EdgeResident source edge := by simpa only [EdgeResident, same] using found
  have captured := SourceRecursiveIntersectionSourceProfile.resident_read source facts edge resident
  have member := SourceRecursiveIntersectionSourceProfile.edge_mem source facts edge.entry.identity edge captured
  have included : edge.entry.key.constraint ∈ guards source := List.mem_map.mpr ⟨edge, member, rfl⟩
  simpa only [same] using included

variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A completed tuple copies only guards admitted by the fixed initial annotation. -/
theorem tuple_heap [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    {tuple : List (EdgeValue Symbol Guard)} {before after : Physical}
    {rows : Option (List (List (Value Symbol Guard)))} (actual : Tuple tuple before rows after)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (resident : Edges before.heap tuple) (closed : ClosedEdges tuple)
    (known : AnnotationHeap annotation before.heap) : AnnotationHeap annotation after.heap := by
  cases actual with
  | contradiction => exact known
  | live _ _ requirements => exact (requirements.verified annotation semantic costs known resident closed).1.annotations

/-- Ordered tuple graphs retain the fixed guard carrier and their complete physical effects. -/
theorem tuples_heap [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    {tuples : List (List (EdgeValue Symbol Guard))} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Tuples tuples before rows after)
    (ready : Ready before) (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple) (known : AnnotationHeap annotation before.heap) :
    Effects before after ∧ AnnotationHeap annotation after.heap ∧ RowsReady after rows := by
  induction actual with
  | nil => exact ⟨.refl _ ready, known, by intro row member; cases member⟩
  | @skip tuple before middle tuples rows after first rest ih =>
      have own := first.verified ready (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self)
      have carrier := tuple_heap annotation first ready.semantic ready.costs
        (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self) known
      have later := ih own.1.ready
        (fun selected member edge included => edge_grows before.heap middle.heap own.1.keeps.growth edge
          (resident selected (List.mem_cons_of_mem _ member) edge included))
        (fun selected member => closed selected (List.mem_cons_of_mem _ member)) carrier
      exact ⟨own.1.trans later.1, later.2⟩
  | @keep tuple before row middle tuples rows after first rest ih =>
      have own := first.verified ready (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self)
      have carrier := tuple_heap annotation first ready.semantic ready.costs
        (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self) known
      have later := ih own.1.ready
        (fun selected member edge included => edge_grows before.heap middle.heap own.1.keeps.growth edge
          (resident selected (List.mem_cons_of_mem _ member) edge included))
        (fun selected member => closed selected (List.mem_cons_of_mem _ member)) carrier
      refine ⟨own.1.trans later.1, later.2.1, ?_⟩
      intro selected member
      rcases List.mem_cons.mp member with rfl | included
      · intro requirement member
        have earlier := own.2 requirement member
        exact ⟨fun value included => later.1.keeps.available value (earlier.1 value included), earlier.2⟩
      · exact later.2.2 selected included

/-- Actual exposure and tuple construction retain both independent annotation invariants. -/
theorem rows_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    {nodes : List (Value Symbol Guard)} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Rows nodes before rows after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (known : AnnotationHeap annotation before.heap) :
    Effects before after ∧ AnnotationHeap annotation after.heap ∧ RowsReady after rows := by
  cases actual with
  | @run edges heap rows after before reads tuples =>
      have own := reads.verified annotation ready.semantic ready.costs known available closed
      have fields := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      have middle : Ready (⟨heap, before.equality⟩ : Physical) :=
        ⟨own.1.semantic, own.1.costs, ready.valid, fields.1.annotations⟩
      have later := tuples_heap annotation tuples middle
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified annotation reads
          ready.semantic ready.costs known available closed tuple member).2.1)
        (fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified annotation reads
          ready.semantic ready.costs known available closed tuple member).2.2) own.1.annotations
      exact ⟨⟨own.1.keeps.trans later.1.keeps, later.1.ready, later.1.grows⟩, later.2⟩

/-- Actual admission derives closedness while retaining arbitrary open skipped pending inputs. -/
theorem run_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    {budget : Nat} {table final : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard))}
    {pending : List (List (Value Symbol Guard))} {before after : Physical}
    (actual : Run budget table pending before final after)
    (ready : Ready before) (available : PendingReady before pending)
    (known : AnnotationHeap annotation before.heap) : Effects before after ∧ AnnotationHeap annotation after.heap := by
  induction actual with
  | done => exact ⟨.refl _ ready, known⟩
  | empty _ _ ih => exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) known
  | skip _ _ _ ih => exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) known
  | @admit budget table nodes before requirements middle pending final after nonempty fresh rows rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed budget table nodes fresh
      have closed := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have own := rows_heap annotation rows ready (available nodes List.mem_cons_self) closed known
      have nextPending : PendingReady middle (requirements.flatten ++ pending) := by
        intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2.2 row rowIn requirement requirementIn).1
        · exact fun value included => own.1.keeps.available value
            (available requirement (List.mem_cons_of_mem _ earlier) value included)
      have later := ih own.1.ready nextPending own.2.1
      exact ⟨own.1.trans later.1, later.2⟩

/-- Initial actual records construct their own exploration while retaining the original finite carrier. -/
theorem entered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (budget : Nat) (pending : List (List (Value Symbol Guard))) (before : Physical)
    (ready : Ready before) (available : PendingReady before pending) :
    ∃ final after, Run budget [] pending before final after ∧ Effects before after ∧
      TableReady after final ∧ final.length ≤ budget ∧
      AnnotationHeap (fun guard => guard ∈ guards before.heap) after.heap := by
  obtain ⟨final, after, actual, effects, table, bound⟩ :=
    SourceCurrentConjunctionWorklist.entered budget pending before ready available
  have carrier := run_heap _ actual ready available (initial before.heap ready.semantic.ready.semantic.1.normal.facts)
  exact ⟨final, after, actual, effects, table, bound, carrier.2⟩

end MicroCFTA.SourceCurrentConjunctionGuardUniverse
