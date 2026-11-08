import MicroCFTA.SourceCurrentConjunctionTupleSoundness
import MicroCFTA.SourceCurrentConjunctionGlobalMemos

/-!
# Three global memo tables through tuple-budget exploration

Overflow and zero admission record only the actual operand exposures.
Positive admission records the full row graph. Each reached state supplies
the premises for the next logical read. The fourth-memo hit skips the body.
These receipts do not establish native lazy demand or memo publication.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleGlobalMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorklist (PendingReady closed closed_values pending_keeps)
open SourceCurrentConjunctionTupleExecution (Admission Run Decision Call)
open SourceCurrentConjunctionGlobalMemos (ExposuresReads RowsReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)

/-- Overflow and zero expose operands; positive admission uses its full allocated row graph. -/
inductive AdmissionReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {budget : Nat} → {nodes : List (Value Symbol Guard)} → {before after : Physical} →
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula} →
    Admission budget nodes before result after → Memos → Memos → Prop where
  | overflow (calls : ExposuresReads exposed memos saved) :
      AdmissionReads (.overflow exposed tooMany) memos saved
  | zero (calls : ExposuresReads exposed memos saved) :
      AdmissionReads (.zero exposed noTuples) memos saved
  | positive {budget predecessor : Nat} {nodes : List (Value Symbol Guard)}
      {before after : Physical} {requirements : List (List (List (Value Symbol Guard)))}
      {actual : Admission budget nodes before (.positive predecessor requirements) after}
      {memos saved : Memos} (calls : RowsReads actual.positive_rows.2 memos saved) :
      AdmissionReads actual memos saved

/-- Worklist receipts follow only visited admissions and their exact returned tables. -/
inductive RunReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {budget : Nat} → {table final : List Entry} → {pending : List (List (Value Symbol Guard))} →
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

/-- The free-list guard and Boolean fixed point add no global reads. -/
inductive DecisionReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] :
    {budget : Nat} → {start : Value Symbol Guard} → {before after : Physical} → {answer : Bool} →
    Decision budget start before answer after → Memos → Memos → Prop where
  | open_input (isOpen : closed start = false) : DecisionReads (.open_input isOpen) memos memos
  | closed (calls : RunReads actual memos saved) : DecisionReads (.closed isClosed actual grown) memos saved

/-- A fourth-memo hit has no body reads; a miss records the actual tuple decision. -/
inductive CallReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] :
    {budget : Nat} → {memo saved : SourceCurrentEmptinessMemo.Memo} → {query : Value Symbol Guard} →
    {before after : Physical} → {answer : Bool} →
    Call budget memo query before answer after saved → Memos → Memos → Prop where
  | hit {budget : Nat} {memo : SourceCurrentEmptinessMemo.Memo} {query original : Value Symbol Guard}
      {answer : Bool} {before : Physical} {memos : Memos}
      (found : memo query.referenceOf = some (original, answer)) :
      CallReads (Call.hit (budget := budget) (before := before) found) memos memos
  | miss (calls : DecisionReads actual memos saved) : CallReads (.miss absent actual) memos saved

/-- Actual admission derives coherent returned tables without any extra read or row execution. -/
theorem admission_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {budget : Nat} {nodes : List (Value Symbol Guard)} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula}
    (actual : Admission budget nodes before result after) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, AdmissionReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases result with
  | overflow =>
      cases actual with
      | overflow exposed tooMany =>
          obtain ⟨saved, reads, coherent, retained, same⟩ :=
            SourceCurrentConjunctionGlobalMemos.exposures_memos exposed
              ready.semantic ready.costs available memos valid
          exact ⟨saved, .overflow (tooMany := tooMany) reads, coherent, retained, same⟩
  | zero =>
      cases actual with
      | zero exposed noTuples =>
          obtain ⟨saved, reads, coherent, retained, same⟩ :=
            SourceCurrentConjunctionGlobalMemos.exposures_memos exposed
              ready.semantic ready.costs available memos valid
          exact ⟨saved, .zero (noTuples := noTuples) reads, coherent, retained, same⟩
  | positive predecessor requirements =>
      obtain ⟨saved, reads, coherent, retained, same⟩ :=
        SourceCurrentConjunctionGlobalMemos.rows_memos actual.positive_rows.2 ready available closed memos valid
      exact ⟨saved, .positive (actual := actual) reads, coherent, retained, same⟩

/-- Every visited tuple admission derives the memo state used by its pending suffix. -/
theorem run_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {budget : Nat} {table final : List Entry} {pending : List (List (Value Symbol Guard))}
    {before after : Physical} (actual : Run budget table pending before final after)
    (ready : Ready before) (available : PendingReady before pending)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, RunReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction actual generalizing memos with
  | done => exact ⟨memos, .done, valid, extends_refl _, rfl⟩
  | empty impossible _ ih =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := ih ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) memos valid
      exact ⟨saved, .empty (impossible := impossible) reads, coherent, retained, same⟩
  | skip nonempty skipped _ ih =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := ih ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) memos valid
      exact ⟨saved, .skip (nonempty := nonempty) (skipped := skipped) reads, coherent, retained, same⟩
  | overflow nonempty fresh admitted _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ fresh).2.1
      have own := admitted.effects ready inputs noFree
      obtain ⟨middle, first, coherent, retained, same⟩ := admission_memos admitted ready inputs noFree memos valid
      obtain ⟨saved, rest, finalValid, finalRetained, finalSame⟩ := ih own.ready
        (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member))) middle coherent
      exact ⟨saved, .overflow (nonempty := nonempty) (fresh := fresh) first rest,
        finalValid, extends_trans retained finalRetained, finalSame.trans same⟩
  | zero nonempty fresh admitted _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ fresh).2.1
      have own := admitted.effects ready inputs noFree
      obtain ⟨middle, first, coherent, retained, same⟩ := admission_memos admitted ready inputs noFree memos valid
      obtain ⟨saved, rest, finalValid, finalRetained, finalSame⟩ := ih own.ready
        (pending_keeps own.keeps (fun nodes member => available nodes (List.mem_cons_of_mem _ member))) middle coherent
      exact ⟨saved, .zero (nonempty := nonempty) (fresh := fresh) first rest,
        finalValid, extends_trans retained finalRetained, finalSame.trans same⟩
  | positive nonempty fresh admitted _ ih =>
      have inputs := available _ List.mem_cons_self
      have noFree := closed_values _ (SourceCurrentConjunctionEmptinessTable.admitted key closed _ _ _ fresh).2.1
      have own := SourceCurrentConjunctionRowsSoundness.rows_verified admitted.positive_rows.2 ready inputs noFree
      obtain ⟨middle, first, coherent, retained, same⟩ := admission_memos admitted ready inputs noFree memos valid
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

/-- The actual decision guard and fixed point retain the worklist's three returned global tables. -/
theorem decision_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {query : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : Decision budget query before answer after) (ready : Ready before)
    (available : Available before.heap query) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, DecisionReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | open_input isOpen => exact ⟨memos, .open_input isOpen, valid, extends_refl _, rfl⟩
  | closed isClosed explored grown =>
      obtain ⟨saved, reads, coherent, retained, same⟩ := run_memos explored ready
        (by
          intro nodes member value included
          cases List.mem_singleton.mp member
          cases List.mem_singleton.mp included
          exact available) memos valid
      exact ⟨saved, .closed (isClosed := isClosed) (grown := grown) reads, coherent, retained, same⟩

/-- Fourth-memo hits skip the body; misses derive coherent tables from their actual decision. -/
theorem call_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {memo saved : SourceCurrentEmptinessMemo.Memo} {query : Value Symbol Guard}
    {before after : Physical} {answer : Bool}
    (actual : Call budget memo query before answer after saved) (ready : Ready before)
    (available : Available before.heap query) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ final, CallReads actual memos final ∧ Valid after.heap final ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases actual with
  | hit found => exact ⟨memos, .hit found, valid, extends_refl _, rfl⟩
  | miss absent decision =>
      obtain ⟨final, reads, coherent, retained, same⟩ := decision_memos decision ready available memos valid
      exact ⟨final, .miss (absent := absent) reads, coherent, retained, same⟩

end MicroCFTA.SourceCurrentConjunctionTupleGlobalMemos
