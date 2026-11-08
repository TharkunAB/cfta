import MicroCFTA.SourceCurrentConjunctionGuard
import MicroCFTA.SourceCurrentConjunctionTupleSoundness
import MicroCFTA.SourceCurrentConjunctionTupleMemo

/-!
# Mu guard observations through tuple admission

Each Mu body retains the same guard observations as its stored ordinary
probe. The proof follows actual admission and worklist graphs.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleGuard
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConstrainedCapGuardHeap (Heap)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionWorker (Physical Table)
open SourceCurrentConjunctionWorklist (PendingReady pending_keeps closed_values)
open SourceCurrentConjunctionTupleExecution (Admission Run Decision Call)

section GenericGuardProofs
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Actual admission preserves the Mu body and probe guard observations. -/
theorem admission (annotation : Guard → Prop) {budget : Nat} {nodes : List (Value Symbol Guard)}
    {before after : Physical Symbol Formula} {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (known : Heap annotation before.heap) :
    Heap annotation after.heap := by
  cases result with
  | overflow =>
      cases actual with
      | overflow exposed _ =>
          exact SourceCurrentConjunctionGuard.exposures annotation exposed ready.semantic ready.costs available known
  | zero => exact SourceCurrentConjunctionGuard.rows annotation actual.zero_rows ready available closed known
  | positive predecessor rows =>
      exact SourceCurrentConjunctionGuard.rows annotation actual.positive_rows.2 ready available closed known

/-- The completed worklist preserves the same observations at its returned heap. -/
theorem run (annotation : Guard → Prop) {budget : Nat} {table final : Table Symbol Formula}
    {pending : List (List (Value Symbol Guard))} {before after : Physical Symbol Formula}
    (actual : Run budget table pending before final after) (ready : Ready before)
    (available : PendingReady before pending) (known : Heap annotation before.heap) : Heap annotation after.heap := by
  induction actual with
  | done => exact known
  | empty _ _ ih => exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) known
  | skip _ _ _ ih => exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) known
  | overflow _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.effects ready inputs noFree
      exact ih own.ready (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member)))
        (admission annotation part ready inputs noFree known)
  | zero _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.effects ready inputs noFree
      exact ih own.ready (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member)))
        (admission annotation part ready inputs noFree known)
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
      · exact admission annotation part ready inputs noFree known

variable [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Both decision branches preserve the Mu guard observations. -/
theorem decision (annotation : Guard → Prop) {budget : Nat} {query : Value Symbol Guard}
    {before after : Physical Symbol Formula} {answer : Bool}
    (actual : Decision budget query before answer after) (ready : Ready before)
    (available : Available before.heap query) (known : Heap annotation before.heap) : Heap annotation after.heap := by
  cases actual with
  | open_input => exact known
  | closed _ actual _ =>
      exact run annotation actual ready
        (by intro nodes member child included; cases List.mem_singleton.mp member; cases List.mem_singleton.mp included; exact available) known
end GenericGuardProofs

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Memo hits and misses preserve the same Mu guard observations. -/
theorem call (annotation : Guard → Prop) {budget : Nat} {query : Node} {memo saved : Memo}
    {before after : Physical Symbol FullSyntax.Formula} {answer : Bool}
    (actual : Call budget memo query before answer after saved) (ready : Ready before)
    (available : Available before.heap query) (known : Heap annotation before.heap) : Heap annotation after.heap := by
  cases actual with
  | hit => exact known
  | miss _ actual => exact decision annotation actual ready available known

/-- Initial readiness constructs a call and preserves its Mu guard observations. -/
theorem complete (annotation : Guard → Prop) (budget : Nat) (memo : Memo) (query : Node)
    (before : Physical Symbol FullSyntax.Formula) (ready : Ready before)
    (available : Available before.heap query) (known : Heap annotation before.heap) :
    ∃ answer after saved, Call budget memo query before answer after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧ Heap annotation after.heap := by
  obtain ⟨answer, after, saved, actual, effects⟩ := SourceCurrentConjunctionTupleMemo.complete budget memo query before ready available
  exact ⟨answer, after, saved, actual, effects, call annotation actual ready available known⟩

end MicroCFTA.SourceCurrentConjunctionTupleGuard
