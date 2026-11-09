import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
import MicroCFTA.SourceCurrentConjunctionSharedWorklistMemos

/-!
# Ordered global memo receipts for shared calls

Successful decisions retain the actual exploration receipt at the same
physical endpoint. Open queries and fourth-memo hits add no global reads.
Misses preserve every actual sample and deferred singleton projection in
execution order. Failed terminal projection receipts remain separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorker (decision call)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "initial" => SourceCurrentConjunctionSharedWorklistStep.initial
local notation "explore" => SourceCurrentConjunctionSharedWorklistRun.explore
local notation "closed" => SourceCurrentConjunctionWorklist.closed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A receipt retains only the branch of the actual successful decision. -/
inductive DecisionReads (p h budget : Nat) (query : Node) (before : Physical) :
    {answer : Bool} → {after : WorkState} →
    (decision p h budget query before = .done answer after) → Memos → Memos → Prop where
  | open_input {answer after actual memos} (isOpen : closed query = false) :
      DecisionReads p h budget query before (answer := answer) (after := after) actual memos memos
  | closed {answer after actual memos saved event} (isClosed : closed query = true)
      (explored : explore p h budget query before = .done event after)
      (calls : SourceCurrentConjunctionSharedWorklistMemos.ExploreReads explored memos saved) :
      DecisionReads p h budget query before (answer := answer) actual memos saved

/-- Fourth-memo hits skip all reads; misses retain the exact decision receipt. -/
inductive CallReads (p h budget : Nat) (memo : Memo) (query : Node) (before : Physical) :
    {answer : Bool} → {saved : Memo} → {after : WorkState} →
    (call p h budget memo query before = .done (answer, saved) after) → Memos → Memos → Prop where
  | hit {answer saved after actual memos original cached}
      (found : memo query.referenceOf = some (original, cached)) :
      CallReads p h budget memo query before (answer := answer) (saved := saved) (after := after) actual memos memos
  | miss {answer saved after actual memos final}
      (absent : memo query.referenceOf = none)
      (decided : decision p h budget query before = .done answer after)
      (calls : DecisionReads p h budget query before decided memos final) :
      CallReads p h budget memo query before (saved := saved) actual memos final

/-- Current inputs derive the same successful decision's ordered memo bundle. -/
theorem decision_memos {p h budget : Nat} {query : Node} {before : Physical}
    {answer : Bool} {after : WorkState}
    (actual : decision p h budget query before = .done answer after)
    (ready : Ready before) (available : Available before.heap query)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, DecisionReads p h budget query before actual memos saved ∧
      Valid after.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases isClosed : closed query with
  | false =>
      rw [SourceCurrentConjunctionSharedWorker.decision_open p h budget query before isClosed] at actual
      cases actual
      exact ⟨memos, .open_input isClosed, valid, extends_refl _, rfl⟩
  | true =>
      simp only [decision, isClosed, ite_true] at actual
      cases explored : explore p h budget query before with
      | failed fault reached => rw [explored] at actual; cases actual
      | done event reached =>
          obtain ⟨saved, reads, coherent, retained, same⟩ :=
            SourceCurrentConjunctionSharedWorklistMemos.explore_memos ready available memos valid explored
          rw [explored] at actual
          dsimp only at actual
          cases materialized : SourceCurrentConjunctionSharedWorklistMaterialization.readTable
              (SourceCurrentConjunctionSharedWorker.endpointCredits p h budget query before) reached with
          | none => rw [materialized] at actual; cases actual
          | some table =>
              rw [materialized] at actual
              dsimp only at actual
              cases grown : SourceCurrentConjunctionEmptinessTable.grow .empty
                  SourceCurrentConjunctionRequirements.key closed table (table.length + 1) (fun _ => false) with
              | none => rw [grown] at actual; cases actual
              | some known =>
                  rw [grown] at actual
                  cases actual
                  exact ⟨saved, .closed isClosed explored reads, coherent, retained, same⟩

/-- Successful hits and misses derive exact global reads without a future bundle. -/
theorem call_memos {p h budget : Nat} {memo saved : Memo} {query : Node} {before : Physical}
    {answer : Bool} {after : WorkState}
    (actual : call p h budget memo query before = .done (answer, saved) after)
    (ready : Ready before) (available : Available before.heap query)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ final, CallReads p h budget memo query before actual memos final ∧
      Valid after.storage.requirements.physical.heap final ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases hit : memo query.referenceOf with
  | some entry =>
      rcases entry with ⟨original, cached⟩
      rw [SourceCurrentConjunctionSharedWorker.call_hit p h budget memo query original before cached hit] at actual
      cases actual
      exact ⟨memos, .hit hit, valid, extends_refl _, rfl⟩
  | none =>
      cases decided : decision p h budget query before with
      | failed fault reached =>
          rw [SourceCurrentConjunctionSharedWorker.call_failed p h budget memo query before reached fault hit decided] at actual
          cases actual
      | done result reached =>
          obtain ⟨final, reads, coherent, retained, same⟩ := decision_memos decided ready available memos valid
          rw [SourceCurrentConjunctionSharedWorker.call_done p h budget memo query before reached result hit decided] at actual
          cases actual
          exact ⟨final, .miss hit decided reads, coherent, retained, same⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorkerMemos
