import MicroCFTA.SourcePruningEnumerationParentProjectionTargets
import MicroCFTA.SourceCurrentConjunctionClassScanCompletion
import MicroCFTA.SourcePrimaryGateEffects
import MicroCFTA.SourceCurrentSecondaryEffects
import MicroCFTA.SourceCurrentConjunctionMemo

/-!
# Projectability through the actual allocated class scan

This draft follows the actual recorded worker endpoints.
It does not assert completion of an arbitrary native prefix.
-/
namespace MicroCFTA.SourcePruningEnumerationConjunctionProjectionHeap
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
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
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual class requirements retain the whole projection heap. -/
theorem requirements_heap
    {tuple : List (EdgeValue Symbol Guard)} {classes : EqualityNormalize.Constraints}
    {before after : State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Req.Requirements tuple classes before requirements after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before tuple) (closed : ClosedEdges tuple) (heap : Heap before) : Heap after :=
  (actual.verified (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
    semantic costs heap resident closed).1.annotations

/-- Equality contradiction and live tuple allocation both retain whole-record projectability. -/
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

/-- Actual exposures and tuple allocations preserve projectability from the original physical input. -/
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
      have current := (reads.verified (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) ready.semantic ready.costs heap available closed).1.annotations
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

/-- The actual dynamic worklist derives projectability without a final-heap supplier. -/
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

/-- Both actual decision branches preserve projectability at their exact physical endpoint. -/
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
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- An actual conjunction memo hit or miss retains projectability without a memo-correctness premise. -/
theorem call_heap
    {budget : Nat} {query : Value Symbol Guard} {before after : Physical} {answer : Bool}
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Available before.heap query) (heap : Heap before.heap) : Heap after.heap := by
  cases actual with
  | hit _ => exact heap
  | miss _ decision => exact decision_heap decision ready available heap

end MicroCFTA.SourcePruningEnumerationConjunctionProjectionHeap


namespace MicroCFTA.SourcePruningEnumerationScanProjectionHeap
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

private theorem query_heap_effects
    (unconstrained : Value Symbol Guard → Bool)
    {paths : Class} {values : List (Value Symbol Guard)}
    {before middle : Checked width} {after : Physical} {anchor : State Symbol Guard}
    {query : Value Symbol Guard} {answer : Bool} {budget : Nat} {memo saved : Memo}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor) query middle)
    (call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) answer after saved)
    (ranges : SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
      (advanceHeap before anchor))
    (proper : ∀ path ∈ paths, path ≠ []) (ready : Ready before)
    (available : Values before.native.machine.heap values)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (heap : Heap before.native.machine.heap) :
    Ready (advancePhysical middle after) ∧ Effects (physical before) after ∧
      Values after.heap values ∧ SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧ Heap after.heap := by
  have initialReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
  obtain ⟨anchorSemantic, anchorReady, _, anchorValues, supported⟩ :=
    SourceCurrentSecondaryProjectionScoped.class_support unconstrained gate ready.semantic
      (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available proper
  have first := SourceCurrentAllocatedGateFields.secondary_class unconstrained gate initialReady available
  have advanced := advance_ready before ⟨anchor, before.operations⟩ ready first.1
  have anchorHeap := (SourceCurrentSecondaryEffects.class_effects (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) unconstrained gate
    ready.semantic ready.costs available heap).2.2.2
  have queryHeap := SourcePruningEnumerationSeededProjectionHeap.seeded_heap unconstrained anchor anchorSemantic anchorReady
    seeded ranges advanced.good first.1.ready advanced.scopedCache advanced.idle anchorValues (grows_refl anchor)
    (by
      intro path member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact supported original present) anchorHeap
  obtain ⟨chosen, reached, completed, queryGood, queryEffects, _, queryScopes, queryIdle, queryAvailable, _⟩ :=
    SourceCurrentAllocatedSeededQuery.false_class_complete unconstrained paths values gate ready.good initialReady
      ready.scopedCache ready.idle available proper ranges
  obtain ⟨rfl, rfl⟩ := seeded.unique completed
  have queryReady : Ready middle :=
    ⟨queryGood, queryEffects.ready.semantic, queryEffects.ready.costs, queryScopes, queryIdle⟩
  have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryEffects.keeps memo correct
  obtain ⟨finalReady, callEffects, finalCorrect, _, _⟩ :=
    memo_effects formulas solver call queryReady queryAvailable queryCorrect
  have afterHeap := SourcePruningEnumerationConjunctionProjectionHeap.call_heap call queryEffects.ready queryAvailable queryHeap
  exact ⟨finalReady, queryEffects.trans callEffects,
    fun value member => callEffects.keeps.available value (queryEffects.keeps.available value (available value member)),
    finalCorrect, afterHeap⟩

/-- The actual class scan retains projectability under its original reached-range and physical contracts. -/
theorem scan_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before memo)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  revert ready available proper correct ranges heap
  induction actual with
  | nil => intro _ _ _ _ _ heap; exact heap
  | selected primary rest ih =>
      intro ready available proper correct ranges heap
      have first := primary_effects unconstrained reaches primary ready available
      have current := (SourcePrimaryGateEffects.class_effects (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) unconstrained reaches primary
        ready.semantic ready.costs available heap).2.2.2
      exact ih first.1 first.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        (SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct) (ranges.1 _ primary) current
  | skipped primary secondary rest ih =>
      intro ready available proper correct ranges heap
      have first := primary_effects unconstrained reaches primary ready available
      have current := (SourcePrimaryGateEffects.class_effects (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) unconstrained reaches primary
        ready.semantic ready.costs available heap).2.2.2
      have second := secondary_effects unconstrained secondary first.1 first.2.2
      have later := (SourceCurrentSecondaryEffects.class_effects (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) unconstrained secondary
        first.1.semantic first.1.costs first.2.2 current).2.2.2
      exact ih second.1 second.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        (SourceCurrentEmptinessMemo.grows formulas solver (first.2.1.trans second.2.1).keeps _ correct)
        (ranges.2.1 _ primary _ secondary) later
  | continued primary secondary seeded call rest ih =>
      intro ready available proper correct ranges heap
      have first := primary_effects unconstrained reaches primary ready available
      have current := (SourcePrimaryGateEffects.class_effects (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) unconstrained reaches primary
        ready.semantic ready.costs available heap).2.2.2
      have reached := ranges.2.2 _ primary _ secondary
      obtain ⟨nextReady, _effects, nextValues, nextCorrect, nextHeap⟩ := query_heap_effects unconstrained
        secondary seeded call reached.1 (proper _ List.mem_cons_self) first.1 first.2.2 formulas solver
        (SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct) current
      exact ih nextReady nextValues (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        nextCorrect (reached.2 _ _ seeded _ _ call) nextHeap
  | stopped primary secondary seeded call =>
      intro ready available proper correct ranges heap
      have first := primary_effects unconstrained reaches primary ready available
      have current := (SourcePrimaryGateEffects.class_effects (fun constraint : Guard => SourcePruningEnumerationConstraint.project constraint ≠ none) unconstrained reaches primary
        ready.semantic ready.costs available heap).2.2.2
      exact (query_heap_effects unconstrained secondary seeded call (ranges.2.2 _ primary _ secondary).1
        (proper _ List.mem_cons_self) first.1 first.2.2 formulas solver
        (SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps _ correct) current).2.2.2.2

end MicroCFTA.SourcePruningEnumerationScanProjectionHeap
