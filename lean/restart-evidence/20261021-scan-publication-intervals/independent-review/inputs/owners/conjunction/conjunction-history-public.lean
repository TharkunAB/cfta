import MicroCFTA.SourceCurrentConjunctionMemo
import MicroCFTA.SourceCurrentConjunctionRowsSoundness
import MicroCFTA.SourceCurrentRequiredPublicationHistory

/-!
# Causal publication intervals through actual conjunction calls

Actual reads and requirement projections provide their own publication
intervals. Ordered tuple and worklist calls compose those same intervals.
Memo hits and open shortcuts retain the constructor heap literally.
-/
namespace MicroCFTA.SourceCurrentConjunctionPublicationHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConjunctionRowsAllocation (Ready Tuple Tuples Rows)
open SourceCurrentConjunctionWorklist (Run PendingReady)
open SourceCurrentNativeMuPublication (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private theorem exposures [DecidableEq (EdgeKey Symbol Guard)] {values : List Node} {before after : Heap}
    {edges : List (List Row)}
    (actual : SourceCurrentConjunctionCompletionReads.Exposures values before edges after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Nonempty (History before after) := by
  induction actual with
  | nil => exact ⟨.refl _⟩
  | cons first rest ih =>
      obtain ⟨initial⟩ := SourceCurrentRequiredPublicationHistory.read first semantic costs
        (available _ List.mem_cons_self)
      have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      obtain ⟨later⟩ := ih effects.2.1 effects.2.2.1
        (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
      exact ⟨.trans initial later⟩

private theorem projections [DecidableEq (EdgeKey Symbol Guard)] {jobs : List (SourceCurrentConjunctionCompletionReads.Job Symbol Guard)}
    {values : List Node} {before after : Heap}
    (actual : SourceCurrentConjunctionCompletionReads.Projections jobs before values after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : ∀ job ∈ jobs, Values before job.1) : Nonempty (History before after) := by
  induction actual with
  | nil => exact ⟨.refl _⟩
  | @cons forest path before value middle jobs values after first rest ih =>
      have inputs := available _ List.mem_cons_self
      obtain ⟨initial⟩ := SourceCurrentRequiredPublicationHistory.forest first semantic costs inputs
      have effects := SourceEqualityProjectionCosts.forest_effects first semantic costs inputs
      obtain ⟨later⟩ := ih effects.2.1 effects.2.2.1
        (fun job member child included => effects.1.available child
          (available job (List.mem_cons_of_mem _ member) child included))
      exact ⟨.trans initial later⟩

private theorem classes [DecidableEq (EdgeKey Symbol Guard)] {forests : List (List Node)} {constraints : EqualityNormalize.Constraints}
    {before after : Heap} {values : List (List Node)}
    (actual : SourceCurrentConjunctionRequirements.ClassRequirements forests constraints before values after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : SourceCurrentConjunctionRequirements.RowsReady before forests) : Nonempty (History before after) := by
  induction actual with
  | nil => exact ⟨.refl _⟩
  | @cons paths before projected middle constraints values after first rest ih =>
      have jobs := SourceCurrentConjunctionCompletionReads.jobs_inputs before forests paths
        (fun forest member => (inputs forest member).1) (fun forest member => (inputs forest member).2)
      have own := first.verified (fun _ => True) semantic costs (by intro _ _ _; trivial) jobs
      obtain ⟨initial⟩ := projections first semantic costs (fun job member => (jobs job member).1)
      obtain ⟨later⟩ := ih own.1.semantic own.1.costs
        (fun forest member => ⟨fun value included => own.1.keeps.available value ((inputs forest member).1 value included),
          (inputs forest member).2⟩)
      exact ⟨.trans initial later⟩

private theorem requirements [DecidableEq (EdgeKey Symbol Guard)] {tuple : List Row} {constraints : EqualityNormalize.Constraints}
    {before after : Heap} {values : List (List Node)}
    (actual : SourceCurrentConjunctionRequirements.Requirements tuple constraints before values after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) : Nonempty (History before after) := by
  cases actual with
  | run _ actual =>
      exact classes actual semantic costs
        (SourceCurrentConjunctionRequirements.tuple_inputs tuple before semantic resident closed)

private theorem tuple [DecidableEq (EdgeKey Symbol Guard)] {edges : List Row} {before after : Physical}
    {values : Option (List (List Node))} (actual : Tuple edges before values after)
    (ready : Ready before) (resident : Edges before.heap edges) (closed : ClosedEdges edges) :
    Nonempty (History before.heap after.heap) := by
  cases actual with
  | contradiction => exact ⟨.refl _⟩
  | live _ _ actual => exact requirements actual ready.semantic ready.costs resident closed

private theorem tuples [DecidableEq (EdgeKey Symbol Guard)] {edges : List (List Row)} {before after : Physical}
    {values : List (List (List Node))} (actual : Tuples edges before values after)
    (ready : Ready before) (resident : ∀ chosen ∈ edges, Edges before.heap chosen)
    (closed : ∀ chosen ∈ edges, ClosedEdges chosen) : Nonempty (History before.heap after.heap) := by
  induction actual with
  | nil => exact ⟨.refl _⟩
  | @skip edges before middle more values after first rest ih =>
      have effects := (first.verified ready (resident edges List.mem_cons_self) (closed edges List.mem_cons_self)).1
      obtain ⟨initial⟩ := tuple first ready (resident edges List.mem_cons_self) (closed edges List.mem_cons_self)
      obtain ⟨later⟩ := ih effects.ready
        (fun selected member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap effects.keeps.growth edge
          (resident selected (List.mem_cons_of_mem _ member) edge included))
        (fun selected member => closed selected (List.mem_cons_of_mem _ member))
      exact ⟨.trans initial later⟩
  | @keep edges before row middle more values after first rest ih =>
      have effects := (first.verified ready (resident edges List.mem_cons_self) (closed edges List.mem_cons_self)).1
      obtain ⟨initial⟩ := tuple first ready (resident edges List.mem_cons_self) (closed edges List.mem_cons_self)
      obtain ⟨later⟩ := ih effects.ready
        (fun selected member edge included => InternedEdgeResidency.edge_grows before.heap middle.heap effects.keeps.growth edge
          (resident selected (List.mem_cons_of_mem _ member) edge included))
        (fun selected member => closed selected (List.mem_cons_of_mem _ member))
      exact ⟨.trans initial later⟩

private theorem rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {nodes : List Node} {before after : Physical}
    {values : List (List (List Node))} (actual : Rows nodes before values after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    Nonempty (History before.heap after.heap) := by
  cases actual with
  | @run edges heap values after before reads allocated =>
      have own := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      obtain ⟨initial⟩ := exposures reads ready.semantic ready.costs available
      have middle : Ready (⟨heap, before.equality⟩ : Physical) :=
        ⟨own.1.semantic, own.1.costs, ready.valid, own.1.annotations⟩
      obtain ⟨later⟩ := tuples allocated middle
        (fun chosen member => (SourceCurrentConjunctionTuples.tuples_verified _ reads
          ready.semantic ready.costs ready.fields available closed chosen member).2.1)
        (fun chosen member => (SourceCurrentConjunctionTuples.tuples_verified _ reads
          ready.semantic ready.costs ready.fields available closed chosen member).2.2)
      exact ⟨.trans initial later⟩

private theorem run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {budget : Nat} {table final : List (SourceCurrentConjunctionEmptinessTable.Entry Node)}
    {pending : List (List Node)} {before after : Physical}
    (actual : Run budget table pending before final after) (ready : Ready before)
    (available : PendingReady before pending) : Nonempty (History before.heap after.heap) := by
  induction actual with
  | done => exact ⟨.refl _⟩
  | empty _ _ ih => exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member))
  | skip _ _ _ ih => exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member))
  | @admit budget table nodes before values middle pending final after _ fresh actual rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted SourceCurrentConjunctionRequirements.key
        SourceCurrentConjunctionWorklist.closed budget table nodes fresh
      have closed := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have own := SourceCurrentConjunctionRowsSoundness.rows_verified actual ready (available nodes List.mem_cons_self) closed
      have nextPending : PendingReady middle (values.flatten ++ pending) := by
        intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2 row rowIn requirement requirementIn).1
        · exact fun value included => own.1.keeps.available value
            (available requirement (List.mem_cons_of_mem _ earlier) value included)
      obtain ⟨initial⟩ := rows actual ready (available nodes List.mem_cons_self) closed
      obtain ⟨later⟩ := ih own.1.ready nextPending
      exact ⟨.trans initial later⟩

private theorem decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {budget : Nat} {value : Node} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionDecision.Decision budget value before answer after)
    (ready : Ready before) (available : Available before.heap value) : Nonempty (History before.heap after.heap) := by
  cases actual with
  | open_input => exact ⟨.refl _⟩
  | closed _ actual _ =>
      exact run actual ready
        (by intro nodes member child included; cases List.mem_singleton.mp member; cases List.mem_singleton.mp included; exact available)

/-- An actual memo call derives its own causal publication interval from physical readiness. -/
theorem call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {budget : Nat} {memo saved : Memo} {query : Node} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved)
    (ready : Ready before) (available : Available before.heap query) :
    Nonempty (History before.heap after.heap) := by
  cases actual with
  | hit => exact ⟨.refl _⟩
  | miss _ actual => exact decision actual ready available

end MicroCFTA.SourceCurrentConjunctionPublicationHistory

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentConjunctionPublicationHistory.call
#print MicroCFTA.SourceCurrentConjunctionPublicationHistory.call
#print axioms MicroCFTA.SourceCurrentConjunctionPublicationHistory.call
