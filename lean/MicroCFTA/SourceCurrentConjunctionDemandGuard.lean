import MicroCFTA.SourceCurrentConjunctionDemandAnnotations
import MicroCFTA.SourceCurrentConjunctionDemandWorklistExecution
import MicroCFTA.SourceCurrentConjunctionDemandSoundness
import MicroCFTA.SourceCurrentConjunctionDemandMemo

/-!
# Causal Mu guard observations through demand worklists

The actual sampled admission supplies each reached heap. Positive admission
derives its returned requirements from the allocated sampled tuples.
These laws concern completed graphs. They do not assert preservation on
failed requirement projections or expose operands that the cursor skips.
Physical annotation laws retain a separate edge annotation predicate.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandGuard
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConstrainedCapGuardHeap (Heap)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionWorker (Physical Table)
open SourceCurrentConjunctionWorklist (PendingReady pending_keeps closed_values)
open SourceCurrentConjunctionDemandExecution (Admission)
open SourceCurrentConjunctionDemandWorklistExecution (Run Decision Call)

section GenericGuardProofs
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every completed admission preserves the original Mu guard observations. -/
theorem admission (annotation : Guard → Prop) {budget : Nat} {nodes : List (Value Symbol Guard)}
    {before after : Physical Symbol Formula} {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (known : Heap annotation before.heap) :
    Heap annotation after.heap :=
  SourceCurrentConjunctionDemandAnnotations.admission_guard_heap annotation actual ready available closed known

/-- The actual worklist retains observations at every completed admission state. -/
theorem run (annotation : Guard → Prop) {budget : Nat} {table final : Table Symbol Formula}
    {pending : List (List (Value Symbol Guard))} {before after : Physical Symbol Formula}
    (actual : Run budget table pending before final after) (ready : Ready before)
    (available : PendingReady before pending) (known : Heap annotation before.heap) : Heap annotation after.heap := by
  induction actual with
  | done => exact known
  | empty _ _ ih | skip _ _ _ ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) known
  | overflow _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.effects ready inputs noFree
      exact ih own.ready
        (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member)))
        (admission annotation part ready inputs noFree known)
  | zero _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.effects ready inputs noFree
      exact ih own.ready
        (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member)))
        (admission annotation part ready inputs noFree known)
  | positive _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.verified ready inputs noFree
      apply ih own.1.ready
      · intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2 row rowIn requirement requirementIn).1
        · exact pending_keeps own.1.keeps
            (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier
      · exact admission annotation part ready inputs noFree known

private theorem admission_annotations (annotation : Guard → Prop) {budget : Nat}
    {nodes : List (Value Symbol Guard)} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (known : SourceEqualityAnnotationHeap.Heap annotation before.heap) :
    SourceEqualityAnnotationHeap.Heap annotation after.heap := by
  obtain ⟨p, h, replay⟩ := SourceCurrentConjunctionDemandExecution.admission_complete actual
  have retained := SourceCurrentConjunctionDemandAnnotations.run_annotation_heap annotation p h budget nodes
    before ready available closed known
  simpa only [replay p h (Nat.le_refl _) (Nat.le_refl _), SourceCurrentConjunctionRowsWorker.Outcome.state]
    using retained

/-- A completed worklist retains the independent physical annotation predicate. -/
theorem run_annotations (annotation : Guard → Prop) {budget : Nat} {table final : Table Symbol Formula}
    {pending : List (List (Value Symbol Guard))} {before after : Physical Symbol Formula}
    (actual : Run budget table pending before final after) (ready : Ready before)
    (available : PendingReady before pending) (known : SourceEqualityAnnotationHeap.Heap annotation before.heap) :
    SourceEqualityAnnotationHeap.Heap annotation after.heap := by
  induction actual with
  | done => exact known
  | empty _ _ ih | skip _ _ _ ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) known
  | overflow _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.effects ready inputs noFree
      exact ih own.ready
        (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member)))
        (admission_annotations annotation part ready inputs noFree known)
  | zero _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.effects ready inputs noFree
      exact ih own.ready
        (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member)))
        (admission_annotations annotation part ready inputs noFree known)
  | positive _ fresh part _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed _ _ _ fresh).2.1
      have own := part.verified ready inputs noFree
      apply ih own.1.ready
      · intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (own.2 row rowIn requirement requirementIn).1
        · exact pending_keeps own.1.keeps
            (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier
      · exact admission_annotations annotation part ready inputs noFree known

variable [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Open and closed decisions preserve the same causal guard heap. -/
theorem decision (annotation : Guard → Prop) {budget : Nat} {query : Value Symbol Guard}
    {before after : Physical Symbol Formula} {answer : Bool}
    (actual : Decision budget query before answer after) (ready : Ready before)
    (available : Available before.heap query) (known : Heap annotation before.heap) : Heap annotation after.heap := by
  cases actual with
  | open_input => exact known
  | closed _ explored _ =>
      exact run annotation explored ready (by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available) known

/-- Completed decisions retain physical annotations without a future-state premise. -/
theorem decision_annotations (annotation : Guard → Prop) {budget : Nat} {query : Value Symbol Guard}
    {before after : Physical Symbol Formula} {answer : Bool}
    (actual : Decision budget query before answer after) (ready : Ready before)
    (available : Available before.heap query) (known : SourceEqualityAnnotationHeap.Heap annotation before.heap) :
    SourceEqualityAnnotationHeap.Heap annotation after.heap := by
  cases actual with
  | open_input => exact known
  | closed _ explored _ =>
      exact run_annotations annotation explored ready (by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available) known
end GenericGuardProofs

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Fourth-memo hits and misses preserve the original guard observations. -/
theorem call (annotation : Guard → Prop) {budget : Nat} {query : Node} {memo saved : Memo}
    {before after : Physical Symbol FullSyntax.Formula} {answer : Bool}
    (actual : Call budget memo query before answer after saved) (ready : Ready before)
    (available : Available before.heap query) (known : Heap annotation before.heap) : Heap annotation after.heap := by
  cases actual with
  | hit => exact known
  | miss _ actual => exact decision annotation actual ready available known

/-- Fourth-memo hits and misses retain the same physical annotation predicate. -/
theorem call_annotations (annotation : Guard → Prop) {budget : Nat} {query : Node} {memo saved : Memo}
    {before after : Physical Symbol FullSyntax.Formula} {answer : Bool}
    (actual : Call budget memo query before answer after saved) (ready : Ready before)
    (available : Available before.heap query) (known : SourceEqualityAnnotationHeap.Heap annotation before.heap) :
    SourceEqualityAnnotationHeap.Heap annotation after.heap := by
  cases actual with
  | hit => exact known
  | miss _ actual => exact decision_annotations annotation actual ready available known

/-- Initial readiness derives a completed call and its causal guard heap. -/
theorem complete (annotation : Guard → Prop) (budget : Nat) (memo : Memo) (query : Node)
    (before : Physical Symbol FullSyntax.Formula) (ready : Ready before)
    (available : Available before.heap query) (known : Heap annotation before.heap) :
    ∃ answer after saved, Call budget memo query before answer after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after ∧ Heap annotation after.heap := by
  obtain ⟨answer, after, saved, actual, effects⟩ :=
    SourceCurrentConjunctionDemandMemo.complete budget memo query before ready available
  exact ⟨answer, after, saved, actual, effects, call annotation actual ready available known⟩

end MicroCFTA.SourceCurrentConjunctionDemandGuard
