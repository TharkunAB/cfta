import MicroCFTA.SourceCurrentConjunctionDemandWorklistExecution
import MicroCFTA.SourceCurrentConjunctionDemandMemos

/-!
# Ordered global memo receipts for demand worklists

Each reached admission contributes its actual sampling calls and reached
tuple calls. Worklist and decision receipts preserve that order. Memo
production and supplied-bundle validation follow the same physical states.
The receipts add no eager exposure or independent logical read schedule.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandWorklistMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorklist (PendingReady closed closed_values pending_keeps)
open SourceCurrentConjunctionDemandWorklistExecution (Run Decision Call)
open SourceCurrentConjunctionDemandMemos (AdmissionReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry Node
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)

/-- Worklist receipts sequence only the admissions that execution reaches. -/
inductive RunReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {budget : Nat} → {table final : List Entry} → {pending : List (List Node)} →
    {before after : Physical} → Run budget table pending before final after → Memos → Memos → Prop where
  | done : RunReads .done memos memos
  | empty (rest : RunReads actual memos saved) : RunReads (.empty impossible actual) memos saved
  | skip (rest : RunReads actual memos saved) : RunReads (.skip nonempty skipped actual) memos saved
  | overflow (first : AdmissionReads admitted memos middle) (rest : RunReads actual middle saved) :
      RunReads (.overflow nonempty fresh admitted actual) memos saved
  | zero (first : AdmissionReads admitted memos middle) (rest : RunReads actual middle saved) :
      RunReads (.zero nonempty fresh admitted actual) memos saved
  | positive (first : AdmissionReads admitted memos middle) (rest : RunReads actual middle saved) :
      RunReads (.positive nonempty fresh admitted actual) memos saved

/-- Neither the free-list test nor the Boolean fixed point adds a read. -/
inductive DecisionReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] :
    {budget : Nat} → {query : Node} → {before after : Physical} → {answer : Bool} →
    Decision budget query before answer after → Memos → Memos → Prop where
  | open_input (isOpen : closed query = false) : DecisionReads (.open_input isOpen) memos memos
  | closed (calls : RunReads actual memos saved) : DecisionReads (.closed isClosed actual grown) memos saved

/-- Hits add no body reads. Misses retain the exact decision receipt. -/
inductive CallReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] :
    {budget : Nat} → {memo saved : Memo} → {query : Node} → {before after : Physical} → {answer : Bool} →
    Call budget memo query before answer after saved → Memos → Memos → Prop where
  | hit {budget : Nat} {memo : Memo} {query original : Node} {answer : Bool} {before : Physical} {memos : Memos}
      (found : memo query.referenceOf = some (original, answer)) :
      CallReads (Call.hit (budget := budget) (before := before) found) memos memos
  | miss (calls : DecisionReads actual memos saved) : CallReads (.miss absent actual) memos saved

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual worklist execution constructs the same ordered global read receipts. -/
theorem run_memos {budget : Nat} {table final : List Entry} {pending : List (List Node)}
    {before after : Physical} (actual : Run budget table pending before final after)
    (ready : Ready before) (available : PendingReady before pending) (memos : Memos)
    (valid : Valid before.heap memos) :
    ∃ saved, RunReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction actual generalizing memos with
  | done => exact ⟨memos, .done, valid, extends_refl _, rfl⟩
  | empty impossible _ ih =>
      obtain ⟨saved, calls, coherent, retained, same⟩ := ih ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) memos valid
      exact ⟨saved, .empty (impossible := impossible) calls, coherent, retained, same⟩
  | skip nonempty skipped _ ih =>
      obtain ⟨saved, calls, coherent, retained, same⟩ := ih ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) memos valid
      exact ⟨saved, .skip (nonempty := nonempty) (skipped := skipped) calls, coherent, retained, same⟩
  | overflow nonempty fresh admitted _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ fresh).2.1
      have own := admitted.verified ready inputs noFree
      obtain ⟨middle, first, coherent, retained, same⟩ :=
        SourceCurrentConjunctionDemandMemos.admission_memos admitted ready inputs noFree memos valid
      obtain ⟨saved, rest, finalValid, finalRetained, finalSame⟩ := ih own.1.ready
        (pending_keeps own.1.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member))) middle coherent
      exact ⟨saved, .overflow (nonempty := nonempty) (fresh := fresh) first rest,
        finalValid, extends_trans retained finalRetained, finalSame.trans same⟩
  | zero nonempty fresh admitted _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ fresh).2.1
      have own := admitted.verified ready inputs noFree
      obtain ⟨middle, first, coherent, retained, same⟩ :=
        SourceCurrentConjunctionDemandMemos.admission_memos admitted ready inputs noFree memos valid
      obtain ⟨saved, rest, finalValid, finalRetained, finalSame⟩ := ih own.1.ready
        (pending_keeps own.1.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member))) middle coherent
      exact ⟨saved, .zero (nonempty := nonempty) (fresh := fresh) first rest,
        finalValid, extends_trans retained finalRetained, finalSame.trans same⟩
  | positive nonempty fresh admitted _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ fresh).2.1
      have own := admitted.verified ready inputs noFree
      obtain ⟨middle, first, coherent, retained, same⟩ :=
        SourceCurrentConjunctionDemandMemos.admission_memos admitted ready inputs noFree memos valid
      obtain ⟨saved, rest, finalValid, finalRetained, finalSame⟩ := ih own.1.ready
        (by
          intro requirement member
          rcases List.mem_append.mp member with generated | earlier
          · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
            exact (own.2 row rowIn requirement requirementIn).1
          · exact pending_keeps own.1.keeps
              (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier)
        middle coherent
      exact ⟨saved, .positive (nonempty := nonempty) (fresh := fresh) first rest,
        finalValid, extends_trans retained finalRetained, finalSame.trans same⟩

private theorem admission_physical {budget : Nat} {nodes : List Node} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula}
    {actual : SourceCurrentConjunctionDemandExecution.Admission budget nodes before result after}
    {memos saved : Memos} (_reads : AdmissionReads actual memos saved) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    Effects before after ∧ (match result with
      | .positive _ rows => SourceCurrentConjunctionRowsAllocation.RowsReady after rows
      | _ => True) := by
  cases result <;> exact actual.verified ready available closed

variable [DecidableEq Node]

/-- The actual decision derives the exact returned global memo bundle. -/
theorem decision_memos {budget : Nat} {query : Node} {before after : Physical} {answer : Bool}
    (actual : Decision budget query before answer after) (ready : Ready before)
    (available : Available before.heap query) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, DecisionReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | open_input isOpen => exact ⟨memos, .open_input isOpen, valid, extends_refl _, rfl⟩
  | closed isClosed explored grown =>
      obtain ⟨saved, calls, coherent, retained, same⟩ := run_memos explored ready
        (by
          intro nodes member value included
          cases List.mem_singleton.mp member
          cases List.mem_singleton.mp included
          exact available) memos valid
      exact ⟨saved, .closed (isClosed := isClosed) (grown := grown) calls, coherent, retained, same⟩

/-- Actual hits and misses derive their own ordered global read receipts. -/
theorem call_memos {budget : Nat} {memo saved : Memo} {query : Node}
    {before after : Physical} {answer : Bool} (actual : Call budget memo query before answer after saved)
    (ready : Ready before) (available : Available before.heap query) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ final, CallReads actual memos final ∧ Valid after.heap final ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases actual with
  | hit found => exact ⟨memos, .hit found, valid, extends_refl _, rfl⟩
  | miss absent actual =>
      obtain ⟨final, calls, coherent, retained, same⟩ := decision_memos actual ready available memos valid
      exact ⟨final, .miss (absent := absent) calls, coherent, retained, same⟩

omit [DecidableEq Node] in
/-- A supplied worklist receipt validates that same bundle at its actual final heap. -/
theorem run_valid {budget : Nat} {table final : List Entry} {pending : List (List Node)}
    {before after : Physical} {actual : Run budget table pending before final after} {memos saved : Memos}
    (reads : RunReads actual memos saved) (ready : Ready before) (available : PendingReady before pending)
    (valid : Valid before.heap memos) :
    Valid after.heap saved ∧ Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction reads with
  | done => exact ⟨valid, extends_refl _, rfl⟩
  | empty _ ih | skip _ ih =>
      exact ih ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) valid
  | overflow first rest ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ (by assumption)).2.1
      have own := admission_physical first ready inputs noFree
      have coherent := SourceCurrentConjunctionDemandMemos.admission_valid first ready inputs noFree valid
      have later := ih own.1.ready
        (pending_keeps own.1.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member))) coherent.1
      exact ⟨later.1, extends_trans coherent.2.1 later.2.1, later.2.2.trans coherent.2.2⟩
  | zero first rest ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ (by assumption)).2.1
      have own := admission_physical first ready inputs noFree
      have coherent := SourceCurrentConjunctionDemandMemos.admission_valid first ready inputs noFree valid
      have later := ih own.1.ready
        (pending_keeps own.1.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member))) coherent.1
      exact ⟨later.1, extends_trans coherent.2.1 later.2.1, later.2.2.trans coherent.2.2⟩
  | positive first rest ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ (by assumption)).2.1
      have own := admission_physical first ready inputs noFree
      have coherent := SourceCurrentConjunctionDemandMemos.admission_valid first ready inputs noFree valid
      have later := ih own.1.ready
        (by
          intro requirement member
          rcases List.mem_append.mp member with generated | earlier
          · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
            exact (own.2 row rowIn requirement requirementIn).1
          · exact pending_keeps own.1.keeps
              (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) requirement earlier)
        coherent.1
      exact ⟨later.1, extends_trans coherent.2.1 later.2.1, later.2.2.trans coherent.2.2⟩

/-- Supplied decision receipts add no logical reads around their worklist. -/
theorem decision_valid {budget : Nat} {query : Node} {before after : Physical} {answer : Bool}
    {actual : Decision budget query before answer after} {memos saved : Memos}
    (reads : DecisionReads actual memos saved) (ready : Ready before) (available : Available before.heap query)
    (valid : Valid before.heap memos) :
    Valid after.heap saved ∧ Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases reads with
  | open_input => exact ⟨valid, extends_refl _, rfl⟩
  | closed calls =>
      exact run_valid calls ready (by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available) valid

/-- Supplied call receipts retain their own memo bundle without changing query tables. -/
theorem call_valid {budget : Nat} {memo saved : Memo} {query : Node} {before after : Physical} {answer : Bool}
    {actual : Call budget memo query before answer after saved} {memos final : Memos}
    (reads : CallReads actual memos final) (ready : Ready before) (available : Available before.heap query)
    (valid : Valid before.heap memos) :
    Valid after.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | hit => exact ⟨valid, extends_refl _, rfl⟩
  | miss calls => exact decision_valid calls ready available valid

end MicroCFTA.SourceCurrentConjunctionDemandWorklistMemos
