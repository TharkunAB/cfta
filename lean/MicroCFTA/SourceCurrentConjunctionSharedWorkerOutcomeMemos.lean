import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
import MicroCFTA.SourceCurrentConjunctionSharedWorkerMemoSoundness
import MicroCFTA.SourceCurrentConjunctionSharedWorklistOutcomeMemos

/-!
# Global memo receipts for every shared worker outcome

Every actual exploration retains its ordered global calls, including its
terminal failed call. Pure decision stages retain the same private state.
Open queries and fourth-memo hits add no global read. The returned global
bundle stays valid at the exact actual physical heap on every outcome.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerOutcomeMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorker (decision call)
open SourceCurrentConjunctionSharedWorkerEffects (decision_state call_state)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "closed" => SourceCurrentConjunctionWorklist.closed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A literal decision records only its selected actual exploration. -/
inductive DecisionReads (p h budget : Nat) (query : Node) (before : Physical) : Memos → Memos → Prop where
  | open_input {memos} (isOpen : closed query = false) : DecisionReads p h budget query before memos memos
  | closed {memos saved} (isClosed : closed query = true)
      (calls : SourceCurrentConjunctionSharedWorklistOutcomeMemos.ExploreReads p h budget query before memos saved) :
      DecisionReads p h budget query before memos saved

/-- Memo hits skip all global reads; misses retain every actual decision read. -/
inductive CallReads (p h budget : Nat) (memo : Memo) (query : Node) (before : Physical) : Memos → Memos → Prop where
  | hit {memos entry} (found : memo query.referenceOf = some entry) : CallReads p h budget memo query before memos memos
  | miss {memos saved} (absent : memo query.referenceOf = none)
      (calls : DecisionReads p h budget query before memos saved) : CallReads p h budget memo query before memos saved

/-- Current inputs derive all global calls at every actual decision endpoint. -/
theorem decision_memos (p h budget : Nat) (query : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap query) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, DecisionReads p h budget query before memos saved ∧
      Valid (decision p h budget query before).state.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases isClosed : closed query with
  | false =>
      refine ⟨memos, .open_input isClosed, ?_, extends_refl _, rfl⟩
      simpa only [decision_state, isClosed, Bool.false_eq_true, ite_false,
        SourceCurrentConjunctionSharedWorklistStep.initial, SourceCurrentConjunctionRequirementRows.initial,
        SourceCurrentConjunctionRequirementCells.initial] using valid
  | true =>
      obtain ⟨saved, calls, coherent, retained, same⟩ :=
        SourceCurrentConjunctionSharedWorklistOutcomeMemos.explore_memos p h budget query before ready available memos valid
      exact ⟨saved, .closed isClosed calls, by simpa only [decision_state, isClosed, ite_true] using coherent,
        retained, same⟩

/-- Every successful or failed memo call derives its exact returned global bundle. -/
theorem call_memos (p h budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap query) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, CallReads p h budget memo query before memos saved ∧
      Valid (call p h budget memo query before).state.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases found : memo query.referenceOf with
  | some entry =>
      refine ⟨memos, .hit found, ?_, extends_refl _, rfl⟩
      simpa only [call_state, found, SourceCurrentConjunctionSharedWorklistStep.initial,
        SourceCurrentConjunctionRequirementRows.initial, SourceCurrentConjunctionRequirementCells.initial] using valid
  | none =>
      obtain ⟨saved, calls, coherent, retained, same⟩ := decision_memos p h budget query before ready available memos valid
      exact ⟨saved, .miss found calls, by simpa only [call_state, found] using coherent, retained, same⟩

/-- A failed call publishes no fourth entry; a successful call supplies its exact saved memo. -/
def returnedMemo (original : Memo) : SourceCurrentConjunctionSharedWorker.Outcome Symbol FullSyntax.Formula (Bool × Memo) → Memo
  | .failed _ _ => original
  | .done result _ => result.2

/-- Current fourth-memo correctness survives every actual call, including failed prefixes. -/
theorem call_fourth (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (p h budget : Nat) (memo : Memo)
    (query : Node) (before : Physical) (ready : Ready before) (available : Available before.heap query)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.heap memo) :
    SourceCurrentEmptinessMemo.Correct formulas solver
        (call p h budget memo query before).state.storage.requirements.physical.heap
        (returnedMemo memo (call p h budget memo query before)) ∧
      SourceCurrentEmptinessMemo.Extends memo (returnedMemo memo (call p h budget memo query before)) ∧
      (match call p h budget memo query before with
       | .failed _ _ => True
       | .done result _ => SourceCurrentEmptinessMemo.AnswerSound formulas solver query result.1) := by
  have effects := (SourceCurrentConjunctionSharedWorkerEffects.call_effects p h budget memo query before ready available).1
  cases actual : call p h budget memo query before with
  | failed fault after =>
      have kept : SourceCurrentConjunctionRowsAllocation.Effects before after.storage.requirements.physical := by
        simpa only [actual, SourceCurrentConjunctionSharedWorker.Outcome.state] using effects
      exact ⟨SourceCurrentEmptinessMemo.grows formulas solver kept.keeps memo correct,
        fun _ _ found => found, trivial⟩
  | done result after =>
      rcases result with ⟨answer, saved⟩
      obtain ⟨coherent, sound, retained⟩ :=
        SourceCurrentConjunctionSharedWorkerMemoSoundness.call_sound formulas solver actual ready available correct
      exact ⟨coherent, retained, sound⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorkerOutcomeMemos
