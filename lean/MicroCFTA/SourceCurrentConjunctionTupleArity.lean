import MicroCFTA.SourcePruningEnumerationConjunctionArity
import MicroCFTA.SourceCurrentConjunctionTupleSoundness

/-!
# Edge-record arity through actual tuple admission

Overflow retains the exposure heap. Zero and positive admission use their
full row receipts. Each worklist suffix starts at the actual returned state.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleArity
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourcePruningEnumerationArityOrigins (Heap)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionWorker (Physical Table)
open SourceCurrentConjunctionWorklist (PendingReady pending_keeps closed_values)
open SourceCurrentConjunctionTupleExecution (Admission Run Decision Call)

section GenericArityProofs
variable {Symbol : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual admission branch preserves whole edge-record arity. -/
theorem admission_heap {budget : Nat} {nodes : List (Value Symbol Guard)}
    {before after : Physical Symbol FullSyntax.Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula}
    (actual : Admission budget nodes before result after) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (heap : Heap before.heap) : Heap after.heap := by
  cases result with
  | overflow =>
      cases actual with
      | overflow exposed _ =>
          exact SourcePruningEnumerationConjunctionArity.exposures_heap exposed
            ready.semantic ready.costs available heap
  | zero =>
      exact SourcePruningEnumerationConjunctionArity.rows_heap actual.zero_rows
        ready available closed heap
  | positive predecessor rows =>
      exact SourcePruningEnumerationConjunctionArity.rows_heap actual.positive_rows.2
        ready available closed heap

/-- All actual worklist branches retain arity at their exact returned heap. -/
theorem run_heap {budget : Nat} {table final : Table Symbol FullSyntax.Formula}
    {pending : List (List (Value Symbol Guard))} {before after : Physical Symbol FullSyntax.Formula}
    (actual : Run budget table pending before final after) (ready : Ready before)
    (available : PendingReady before pending) (heap : Heap before.heap) : Heap after.heap := by
  induction actual with
  | done => exact heap
  | empty _ _ ih | skip _ _ _ ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) heap
  | overflow _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.effects ready inputs noFree
      exact ih own.ready
        (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member)))
        (admission_heap part ready inputs noFree heap)
  | zero _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.effects ready inputs noFree
      exact ih own.ready
        (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member)))
        (admission_heap part ready inputs noFree heap)
  | positive _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := SourceCurrentConjunctionRowsSoundness.rows_verified part.positive_rows.2 ready inputs noFree
      apply ih own.1.ready
      · intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2 row rowIn requirement requirementIn).1
        · exact pending_keeps own.1.keeps
            (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier
      · exact admission_heap part ready inputs noFree heap

variable [DecidableEq (Value Symbol Guard)]

/-- Open and closed decisions preserve whole edge-record arity. -/
theorem decision_heap {budget : Nat} {query : Value Symbol Guard}
    {before after : Physical Symbol FullSyntax.Formula} {answer : Bool}
    (actual : Decision budget query before answer after) (ready : Ready before)
    (available : Available before.heap query) (heap : Heap before.heap) : Heap after.heap := by
  cases actual with
  | open_input _ => exact heap
  | closed _ explored _ =>
      apply run_heap explored ready
      · intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available
      · exact heap
end GenericArityProofs

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Actual fourth-memo hits and misses retain arity without a memo-correctness premise. -/
theorem call_heap {budget : Nat} {query : Node}
    {before after : Physical Symbol FullSyntax.Formula} {answer : Bool}
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    (actual : Call budget memo query before answer after saved) (ready : Ready before)
    (available : Available before.heap query) (heap : Heap before.heap) : Heap after.heap := by
  cases actual with
  | hit _ => exact heap
  | miss _ decision => exact decision_heap decision ready available heap

end MicroCFTA.SourceCurrentConjunctionTupleArity
