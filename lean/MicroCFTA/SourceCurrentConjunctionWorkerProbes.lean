import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentConjunctionWorkerWarmEffects
import MicroCFTA.SourceCurrentConjunctionRowsProbes

set_option autoImplicit false
open scoped Classical

/-! Probe and readiness preservation at actual conjunction endpoints. -/
namespace MicroCFTA.SourceCurrentConjunctionWorkerProbes
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionWorker
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
local notation "Heap" => InternedFreshOrdinaryProbeHeap.Heap

section Generic
variable {Formula : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- Every actual worklist outcome retains clean probes at its reached heap. -/
theorem explore_heap (p h budget : Nat) (table : SourceCurrentConjunctionWorker.Table Symbol Formula)
    (pending : List (List (Value Symbol Guard))) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : Heap before.heap)
    (inputs : ∀ nodes ∈ pending, Values before.heap nodes ∧ ClosedValues nodes) :
    Heap (SourceCurrentConjunctionWorker.explore p h budget table pending before).state.heap := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
    induction pending generalizing table before with
    | nil => simpa only [SourceCurrentConjunctionWorker.explore, Outcome.state] using probes
    | cons nodes rest tail =>
      rw [SourceCurrentConjunctionWorker.explore]
      split
      · exact tail table before ready probes
          (fun group member => inputs group (List.mem_cons_of_mem _ member))
      · split
        · exact tail table before ready probes
            (fun group member => inputs group (List.mem_cons_of_mem _ member))
        · have positive := (SourceCurrentConjunctionEmptinessTable.admitted
            SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed
            budget table nodes (Bool.eq_false_iff.mpr (by assumption))).1
          have produced := SourceCurrentConjunctionRowsWarmEffects.rows_effects p h nodes before ready
            (inputs nodes List.mem_cons_self).1
          have first : Effects before (SourceCurrentConjunctionRowsWorker.rows p h nodes before).state := by
            refine Eq.mp ?_ produced
            congr <;> exact Subsingleton.elim _ _
          have producedProbes := SourceCurrentConjunctionRowsProbes.rows_heap p h nodes before ready probes
            (inputs nodes List.mem_cons_self).1
          have clean : Heap (SourceCurrentConjunctionRowsWorker.rows p h nodes before).state.heap := by
            refine Eq.mp ?_ producedProbes
            congr <;> exact Subsingleton.elim _ _
          have returned := (SourceCurrentConjunctionRowsWorkerEffects.rows_effects p h nodes before
            ready.semantic.ready.semantic ready.semantic.ready.covered
            (inputs nodes List.mem_cons_self).1 (inputs nodes List.mem_cons_self).2).2.2.2.2
          cases actual : SourceCurrentConjunctionRowsWorker.rows p h nodes before with
          | done requirements middle =>
            simp only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] at first clean
            rw [actual] at returned
            have remaining : ∀ group ∈ requirements.flatten ++ rest,
                Values middle.heap group ∧ ClosedValues group := by
              intro group member
              rcases List.mem_append.mp member with fresh | old
              · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp fresh
                exact returned row rowIn group groupIn
              · exact ⟨fun value included => first.keeps.available value
                    ((inputs group (List.mem_cons_of_mem _ old)).1 value included),
                  (inputs group (List.mem_cons_of_mem _ old)).2⟩
            exact smaller (budget - 1) (by omega) (⟨nodes, requirements⟩ :: table)
              (requirements.flatten ++ rest) middle first.ready clean remaining
          | failed fault after =>
            simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state, Outcome.state] using clean

/-- Every actual fixed-point outcome retains probes from the original query heap. -/
theorem decision_heap (p h budget : Nat) (query : Value Symbol Guard)
    (before : Physical Symbol Formula) (ready : Ready before) (probes : Heap before.heap)
    (available : Available before.heap query) (closed : query.free = []) :
    Heap (SourceCurrentConjunctionWorker.decision p h budget query before).state.heap := by
  unfold SourceCurrentConjunctionWorker.decision
  split
  · have inputs : ∀ nodes ∈ [[query]], Values before.heap nodes ∧ ClosedValues nodes := by
      intro nodes member
      have same := List.mem_singleton.mp member
      subst nodes
      constructor
      · intro value member
        have same := List.mem_singleton.mp member
        subst value
        exact available
      · intro value member
        have same := List.mem_singleton.mp member
        subst value
        exact closed
    have explored := explore_heap p h budget [] [[query]] before ready probes inputs
    cases actual : SourceCurrentConjunctionWorker.explore p h budget [] [[query]] before with
    | failed fault after =>
      simpa only [actual, Outcome.bind, Outcome.state] using explored
    | done table after =>
      simp only [actual, Outcome.state] at explored
      simp only [Outcome.bind]
      split <;> exact explored
  · exact probes
end Generic

local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State

/-- Memo hits and every actual miss outcome retain clean Mu probes. -/
theorem call_heap (p h budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (ready : Ready before) (probes : Heap before.heap)
    (available : Available before.heap query) (closed : query.free = []) :
    Heap (SourceCurrentConjunctionWorker.call p h budget memo query before).state.heap := by
  unfold SourceCurrentConjunctionWorker.call
  split
  · exact probes
  · have decided := decision_heap p h budget query before ready probes available closed
    cases actual : SourceCurrentConjunctionWorker.decision p h budget query before with
    | done answer after => simpa only [actual, Outcome.bind, Outcome.state] using decided
    | failed fault after => simpa only [actual, Outcome.bind, Outcome.state] using decided

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The original caller context supplies probes at the literal allocated endpoint. -/
theorem allocated_call_heap {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    (p h budget : Nat) (query : Node) (before : Caller width) (memos : EndpointMemoGateTrace.Memos)
    (context : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth
    Heap actual.state.native.machine.heap := by
  change Heap (SourceCurrentAllocatedNativeEffects.physical
    (SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth).state).heap
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked context.ready.good
    context.ready.semantic context.ready.costs
  have produced := call_heap p h budget before.fourth query
    (SourceCurrentAllocatedNativeEffects.physical before.checked) ready context.probes available closed
  have clean : Heap (SourceCurrentConjunctionWorker.call p h budget before.fourth query
      (SourceCurrentAllocatedNativeEffects.physical before.checked)).state.heap := by
    refine Eq.mp ?_ produced
    congr; exact Subsingleton.elim _ _
  cases actual : SourceCurrentConjunctionWorker.call p h budget before.fourth query
      (SourceCurrentAllocatedNativeEffects.physical before.checked) with
  | done output after =>
    rcases output with ⟨answer, saved⟩
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at clean
    simpa only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state,
      SourceCurrentAllocatedQueryMemo.physical_advance] using clean
  | failed fault after =>
    simp only [actual, SourceCurrentConjunctionWorker.Outcome.state] at clean
    simpa only [SourceCurrentAllocatedConjunctionWorker.call, actual,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state,
      SourceCurrentAllocatedQueryMemo.physical_advance] using clean

end MicroCFTA.SourceCurrentConjunctionWorkerProbes
