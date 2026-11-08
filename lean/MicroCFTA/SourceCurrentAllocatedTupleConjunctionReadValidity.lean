import MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity
import MicroCFTA.SourceCurrentConjunctionDemandWorklistMemos

/-!
# Validity of supplied tuple-budget read receipts

The proof uses each supplied receipt and its exact returned bundle.
Overflow and zero use the actual repeated demand reads. Positive admission
adds its actual allocated-tuple reads. Actual effects supply the next read premises.
The proof does not compare different read schedules.
-/
namespace MicroCFTA.SourceCurrentAllocatedTupleConjunctionReadValidity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects RowsReady)
open SourceCurrentConjunctionWorklist (PendingReady closed closed_values pending_keeps)
open SourceCurrentConjunctionDemandExecution (Admission)
open SourceCurrentConjunctionDemandWorklistExecution (Run Decision Call)
open SourceCurrentConjunctionDemandMemos (AdmissionReads)
open SourceCurrentConjunctionDemandWorklistMemos (RunReads DecisionReads CallReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem admission_physical [DecidableEq Symbol]
    {budget : Nat} {nodes : List (Value Symbol Guard)} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula}
    {actual : Admission budget nodes before result after} {memos final : Memos}
    (_reads : AdmissionReads actual memos final) (ready : Ready before)
    (available : Values before.heap nodes) (noFree : ClosedValues nodes) :
    Effects before after ∧
      (match result with | .positive _ rows => RowsReady after rows | _ => True) := by
  cases result <;> exact actual.verified ready available noFree

/-- Supplied admission reads retain their own coherent global bundle. -/
theorem admission [DecidableEq Symbol]
    {budget : Nat} {nodes : List (Value Symbol Guard)} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula}
    {actual : Admission budget nodes before result after} {memos final : Memos}
    (reads : AdmissionReads actual memos final) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  exact SourceCurrentConjunctionDemandMemos.admission_valid reads ready available closed valid

/-- Actual admissions supply all premises for the supplied pending suffix receipts. -/
theorem run [DecidableEq Symbol]
    {budget : Nat} {table entered : List Entry} {pending : List (List (Value Symbol Guard))}
    {before after : Physical} {actual : Run budget table pending before entered after} {memos final : Memos}
    (reads : RunReads actual memos final) (ready : Ready before) (available : PendingReady before pending)
    (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  induction reads with
  | done => exact ⟨valid, extends_refl _, rfl⟩
  | empty _ ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) valid
  | skip _ ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) valid
  | overflow first rest ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ (by assumption)).2.1
      have own := admission_physical first ready inputs noFree
      have firstMemo := admission first ready inputs noFree valid
      have later := ih own.1.ready
        (pending_keeps own.1.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member))) firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩
  | zero first rest ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ (by assumption)).2.1
      have own := admission_physical first ready inputs noFree
      have firstMemo := admission first ready inputs noFree valid
      have later := ih own.1.ready
        (pending_keeps own.1.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member))) firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩
  | positive first rest ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ (by assumption)).2.1
      have own := admission_physical first ready inputs noFree
      have firstMemo := admission first ready inputs noFree valid
      have later := ih own.1.ready
        (by
          intro requirement member
          rcases List.mem_append.mp member with generated | earlier
          · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
            exact (own.2 row rowIn requirement requirementIn).1
          · exact pending_keeps own.1.keeps
              (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier)
        firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩

/-- The supplied decision adds no reads around its actual worklist. -/
theorem decision [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {query : Value Symbol Guard} {before after : Physical} {answer : Bool}
    {actual : Decision budget query before answer after} {memos final : Memos}
    (reads : DecisionReads actual memos final) (ready : Ready before) (available : Available before.heap query)
    (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | open_input => exact ⟨valid, extends_refl _, rfl⟩
  | closed calls =>
      exact run calls ready (by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available) valid

/-- Supplied fourth-memo hits and misses derive validity for that exact returned bundle. -/
theorem call [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {memo saved : SourceCurrentEmptinessMemo.Memo} {query : Value Symbol Guard}
    {before after : Physical} {answer : Bool}
    {actual : Call budget memo query before answer after saved} {memos final : Memos}
    (reads : CallReads actual memos final) (ready : Ready before) (available : Available before.heap query)
    (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | hit => exact ⟨valid, extends_refl _, rfl⟩
  | miss calls => exact decision calls ready available valid

end MicroCFTA.SourceCurrentAllocatedTupleConjunctionReadValidity
