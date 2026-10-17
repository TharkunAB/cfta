import MicroCFTA.SourceCurrentConjunctionGuardUniverse
import MicroCFTA.SourceCurrentConjunctionMemo
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard

/-!
# Causal Mu guard observations through actual conjunction calls

Actual reads and projections retain stored body-to-probe observations.
Ordered row and worklist graphs pass that heap to each reached operation.
The guard predicate imposes no restriction on unrelated physical edges.
-/
namespace MicroCFTA.SourceCurrentConjunctionGuard
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConstrainedCapGuardHeap (Heap)
open SourceCurrentConjunctionRowsAllocation (Ready Effects Tuple Tuples Rows)
open SourceCurrentConjunctionWorklist (Run PendingReady)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

section General
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual ordered exposures retain the earlier causal guard observations. -/
theorem exposures (annotation : Guard → Prop)
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (List (EdgeValue Symbol Guard))}
    (actual : SourceCurrentConjunctionCompletionReads.Exposures values before edges after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (known : Heap annotation before) : Heap annotation after := by
  induction actual with
  | nil => exact known
  | @cons value before edges middle values more after first rest ih =>
      have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      have guards := SourceCurrentConstrainedCapProjectionGuard.read annotation first semantic costs
        (available _ List.mem_cons_self) known
      exact ih effects.2.1 effects.2.2.1
        (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member))) guards

/-- Source projection jobs need available forests, without whole-forest closedness. -/
theorem projections (annotation : Guard → Prop)
    {jobs : List (SourceCurrentConjunctionCompletionReads.Job Symbol Guard)}
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : SourceCurrentConjunctionCompletionReads.Projections jobs before values after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : ∀ job ∈ jobs, Values before job.1) (known : Heap annotation before) : Heap annotation after := by
  induction actual with
  | nil => exact known
  | @cons forest path before value middle jobs values after first rest ih =>
      have inputs := available _ List.mem_cons_self
      have effects := SourceEqualityProjectionCosts.forest_effects first semantic costs inputs
      have guards := SourceCurrentConstrainedCapProjectionGuard.forest annotation first semantic costs inputs known
      exact ih effects.2.1 effects.2.2.1
        (fun job member child included => effects.1.available child
          (available job (List.mem_cons_of_mem _ member) child included)) guards

/-- Actual class requirements retain the causal heap at each source-ordered projection. -/
theorem classes (annotation : Guard → Prop)
    {forests : List (List (Value Symbol Guard))} {constraints : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {values : List (List (Value Symbol Guard))}
    (actual : SourceCurrentConjunctionRequirements.ClassRequirements forests constraints before values after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : SourceCurrentConjunctionRequirements.RowsReady before forests) (known : Heap annotation before) :
    Heap annotation after := by
  induction actual with
  | nil => exact known
  | @cons paths before projected middle constraints values after first rest ih =>
      have jobs := SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
        (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2)
      have own := first.verified (fun _ => True) semantic costs (by intro _ _ _; trivial) jobs
      have guards := projections annotation first semantic costs (fun job member => (jobs job member).1) known
      exact ih own.1.semantic own.1.costs
        (fun forest member => ⟨fun value included => own.1.keeps.available value ((inputs forest member).1 value included),
          (inputs forest member).2⟩) guards

/-- Tuple requirements reuse actual input records and their causal guard observations. -/
theorem requirements (annotation : Guard → Prop)
    {tuple : List (EdgeValue Symbol Guard)} {constraints : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {values : List (List (Value Symbol Guard))}
    (actual : SourceCurrentConjunctionRequirements.Requirements tuple constraints before values after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) (known : Heap annotation before) : Heap annotation after := by
  cases actual with
  | run _ actual =>
      exact classes annotation actual semantic costs
        (SourceCurrentConjunctionRequirements.tuple_inputs tuple before semantic resident closed) known
end General

section Rows
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Equality-only tuple allocation changes no causal guard observation. -/
theorem tuple (annotation : Guard → Prop)
    {edges : List (EdgeValue Symbol Guard)} {before after : Physical}
    {values : Option (List (List (Value Symbol Guard)))} (actual : Tuple edges before values after)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap)
    (resident : Edges before.heap edges) (closed : ClosedEdges edges) (known : Heap annotation before.heap) :
    Heap annotation after.heap := by
  cases actual with
  | contradiction => exact known
  | live _ _ actual => exact requirements annotation actual semantic costs resident closed known

/-- Ordered tuple allocation retains the causal heap through both skip and keep branches. -/
theorem tuples (annotation : Guard → Prop)
    {edges : List (List (EdgeValue Symbol Guard))} {before after : Physical}
    {values : List (List (List (Value Symbol Guard)))} (actual : Tuples edges before values after)
    (ready : Ready before) (resident : ∀ chosen ∈ edges, Edges before.heap chosen)
    (closed : ∀ chosen ∈ edges, ClosedEdges chosen) (known : Heap annotation before.heap) : Heap annotation after.heap := by
  induction actual with
  | nil => exact known
  | @skip edges before middle more values after first rest ih =>
      have effects := (first.verified ready (resident edges List.mem_cons_self) (closed edges List.mem_cons_self)).1
      exact ih effects.ready
        (fun selected member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap effects.keeps.growth edge
          (resident selected (List.mem_cons_of_mem _ member) edge included))
        (fun selected member => closed selected (List.mem_cons_of_mem _ member))
        (tuple annotation first ready.semantic ready.costs (resident edges List.mem_cons_self) (closed edges List.mem_cons_self) known)
  | @keep edges before row middle more values after first rest ih =>
      have effects := (first.verified ready (resident edges List.mem_cons_self) (closed edges List.mem_cons_self)).1
      exact ih effects.ready
        (fun selected member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap effects.keeps.growth edge
          (resident selected (List.mem_cons_of_mem _ member) edge included))
        (fun selected member => closed selected (List.mem_cons_of_mem _ member))
        (tuple annotation first ready.semantic ready.costs (resident edges List.mem_cons_self) (closed edges List.mem_cons_self) known)

variable [DecidableEq Symbol]

/-- Actual exposures and requirements retain the causal heap independently of row guard validity. -/
theorem rows (annotation : Guard → Prop)
    {nodes : List (Value Symbol Guard)} {before after : Physical}
    {values : List (List (List (Value Symbol Guard)))} (actual : Rows nodes before values after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (known : Heap annotation before.heap) : Heap annotation after.heap := by
  cases actual with
  | @run edges heap values after before reads allocated =>
      have own := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      have guards := exposures annotation reads ready.semantic ready.costs available known
      have middle : Ready (⟨heap, before.equality⟩ : Physical) :=
        ⟨own.1.semantic, own.1.costs, ready.valid, own.1.annotations⟩
      exact tuples annotation allocated middle
        (fun chosen member => (SourceCurrentConjunctionTuples.tuples_verified _ reads
          ready.semantic ready.costs ready.fields available closed chosen member).2.1)
        (fun chosen member => (SourceCurrentConjunctionTuples.tuples_verified _ reads
          ready.semantic ready.costs ready.fields available closed chosen member).2.2) guards

/-- Actual worklist admission derives its own closedness and retains open skipped pending inputs. -/
theorem run (annotation : Guard → Prop)
    {budget : Nat} {table final : List (SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard))}
    {pending : List (List (Value Symbol Guard))} {before after : Physical}
    (actual : Run budget table pending before final after) (ready : Ready before)
    (available : PendingReady before pending) (known : Heap annotation before.heap) : Heap annotation after.heap := by
  induction actual with
  | done => exact known
  | empty _ _ ih => exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) known
  | skip _ _ _ ih => exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) known
  | @admit budget table nodes before values middle pending final after _ fresh actual rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted SourceCurrentConjunctionRequirements.key
        SourceCurrentConjunctionWorklist.closed budget table nodes fresh
      have closed := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have own := SourceCurrentConjunctionGuardUniverse.rows_heap (fun _ => True) actual ready
        (available nodes List.mem_cons_self) closed (by intro _ _ _; trivial)
      have nextPending : PendingReady middle (values.flatten ++ pending) := by
        intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2.2 row rowIn requirement requirementIn).1
        · exact fun value included => own.1.keeps.available value
            (available requirement (List.mem_cons_of_mem _ earlier) value included)
      exact ih own.1.ready nextPending (rows annotation actual ready (available nodes List.mem_cons_self) closed known)

variable [DecidableEq (Value Symbol Guard)]

/-- Both open shortcuts and actual closed exploration retain the same causal observations. -/
theorem decision (annotation : Guard → Prop)
    {budget : Nat} {value : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionDecision.Decision budget value before answer after)
    (ready : Ready before) (available : Available before.heap value) (known : Heap annotation before.heap) :
    Heap annotation after.heap := by
  cases actual with
  | open_input => exact known
  | closed _ actual _ =>
      exact run annotation actual ready
        (by intro nodes member child included; cases List.mem_singleton.mp member; cases List.mem_singleton.mp included; exact available) known
end Rows

section Current
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A memo hit retains the heap; a miss retains observations through its actual decision. -/
theorem call (annotation : Guard → Prop)
    {budget : Nat} {memo saved : Memo} {value : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionMemo.Call budget memo value before answer after saved)
    (ready : Ready before) (available : Available before.heap value) (known : Heap annotation before.heap) :
    Heap annotation after.heap := by
  cases actual with
  | hit => exact known
  | miss _ actual => exact decision annotation actual ready available known

/-- Initial physical facts construct an actual call and retain its causal heap without a body premise. -/
theorem complete (annotation : Guard → Prop) (budget : Nat) (memo : Memo) (value : Value Symbol Guard)
    (before : Physical) (ready : Ready before) (available : Available before.heap value) (known : Heap annotation before.heap) :
    ∃ answer after saved, SourceCurrentConjunctionMemo.Call budget memo value before answer after saved ∧
      Effects before after ∧ Heap annotation after.heap := by
  obtain ⟨answer, after, saved, actual, effects⟩ := SourceCurrentConjunctionMemo.complete budget memo value before ready available
  exact ⟨answer, after, saved, actual, effects, call annotation actual ready available known⟩
end Current
end MicroCFTA.SourceCurrentConjunctionGuard
