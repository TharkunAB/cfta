import MicroCFTA.SourceCurrentOutcomeCursorReadDeterminism
import MicroCFTA.SourceCurrentOutcomeRequirementReadDeterminism
import MicroCFTA.SourceCurrentConjunctionSharedWorkerOutcomeMemos

/-!
# Validity of the supplied shared call receipt

Each receipt follows one actual branch and its ordered read sequence.
Two receipts with the same inputs and initial bundle return the same
bundle. Current readiness and residency then prove validity for the
supplied receipt at the literal successful or failed worker endpoint.
-/
namespace MicroCFTA.SourceCurrentSharedCallReadValidity
open InternedConstructorTemplates
open SourceCurrentConjunctionSharedWorklistOutcomeMemos
open SourceCurrentConjunctionSharedWorkerOutcomeMemos (DecisionReads CallReads)
open SourceCurrentConjunctionRequirementCellsOutcomeMemos (ForceReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Task" => SourceCurrentConjunctionSharedWorklistStep.Task Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A visit has one returned global bundle for its same initial bundle. -/
theorem visit_unique {h : Nat} {nodes : List Node} {rest : List Task} {before : WorkState}
    {memos first last : Memos} (one : VisitReads h nodes rest before memos first)
    (two : VisitReads h nodes rest before memos last) : first = last := by
  cases one <;> cases two <;> simp_all
  exact SourceCurrentOutcomeCursorReadDeterminism.sample_unique (by assumption) (by assumption)

/-- One actual transition preserves the unique force-before-visit memo order. -/
theorem step_unique {p h : Nat} {before : WorkState} {memos first last : Memos}
    (one : StepReads p h before memos first) (two : StepReads p h before memos last) : first = last := by
  cases one with
  | drained pending => cases two <;> simp_all
  | nodes pending calls =>
      cases two <;> simp_all
      exact visit_unique calls (by assumption)
  | requirements_nil pending => cases two <;> simp_all
  | requirement_failed pending forced calls =>
      cases two <;> simp_all
      exact SourceCurrentOutcomeRequirementReadDeterminism.force_unique calls (by assumption)
  | requirement_done pending forced first last =>
      cases two with
      | drained other => simp_all
      | nodes other calls => simp_all
      | requirements_nil other => simp_all
      | requirement_failed other observed calls => simp_all
      | requirement_done other observed earlier later =>
          have sameTasks := pending.symm.trans other
          simp only [List.cons.injEq,
            SourceCurrentConjunctionSharedWorklistStep.Task.requirements.injEq] at sameTasks
          rcases sameTasks with ⟨⟨rfl, rfl⟩, rfl⟩
          obtain ⟨rfl, rfl⟩ := SourceCurrentConjunctionRequirementCells.Outcome.done.inj
            (forced.symm.trans observed)
          have same := SourceCurrentOutcomeRequirementReadDeterminism.force_unique first earlier
          cases same
          exact visit_unique last later
      | rows_failed other observed => simp_all
      | rows_none other observed => simp_all
      | rows_live other observed => simp_all
  | rows_failed pending observed => cases two <;> simp_all
  | rows_none pending observed => cases two <;> simp_all
  | rows_live pending observed => cases two <;> simp_all

/-- The same actual finite run has one returned global bundle. -/
theorem run_unique {p h : Nat} {before : WorkState}
    {outcome : SourceCurrentConjunctionSharedWorklistStep.Outcome Symbol FullSyntax.Formula}
    {actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome}
    {memos first last : Memos} (one : RunReads actual memos first) (two : RunReads actual memos last) : first = last := by
  induction one generalizing last with
  | @failed before after fault observed memos saved calls =>
      cases two with
      | failed other => exact step_unique calls other
      | @more before middle outcome another tail memos current result other later =>
          cases observed.symm.trans another
  | @drained before after observed memos saved calls =>
      cases two with
      | drained other => exact step_unique calls other
      | @more before middle outcome another tail memos current result other later =>
          have impossible := SourceCurrentConjunctionSharedWorklistStep.Outcome.done.inj
            (observed.symm.trans another)
          cases impossible.1
  | @more before middle outcome observed tail memos current saved first rest ih =>
      cases two with
      | @failed before after fault another memos result other =>
          cases observed.symm.trans another
      | @drained before after another memos result other =>
          have impossible := SourceCurrentConjunctionSharedWorklistStep.Outcome.done.inj
            (observed.symm.trans another)
          cases impossible.1
      | @more before later outcome another suffix memos intermediate result other following =>
          have endpoints := SourceCurrentConjunctionSharedWorklistStep.Outcome.done.inj
            (observed.symm.trans another)
          cases endpoints.2
          have same := step_unique first other
          cases same
          exact ih following

/-- Internally derived exploration graphs preserve the same bundle uniqueness. -/
theorem explore_unique {p h budget : Nat} {query : Node} {before : Physical} {memos first last : Memos}
    (one : ExploreReads p h budget query before memos first)
    (two : ExploreReads p h budget query before memos last) : first = last := run_unique one two

/-- The literal closed or open decision selects one actual read schedule. -/
theorem decision_unique {p h budget : Nat} {query : Node} {before : Physical} {memos first last : Memos}
    (one : DecisionReads p h budget query before memos first)
    (two : DecisionReads p h budget query before memos last) : first = last := by
  cases one <;> cases two <;> simp_all
  exact explore_unique (by assumption) (by assumption)

/-- The literal memo hit or miss selects one actual returned bundle. -/
theorem call_unique {p h budget : Nat} {memo : Memo} {query : Node} {before : Physical} {memos first last : Memos}
    (one : CallReads p h budget memo query before memos first)
    (two : CallReads p h budget memo query before memos last) : first = last := by
  cases one <;> cases two <;> simp_all
  exact decision_unique (by assumption) (by assumption)

variable [DecidableEq Node]

/-- Current inputs prove validity for the supplied all-outcome shared call receipt. -/
theorem call (p h budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (available : InternedProbeProvenance.Available before.heap query)
    {memos final : Memos} (valid : Valid before.heap memos)
    (reads : CallReads p h budget memo query before memos final) :
    Valid (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state.storage.requirements.physical.heap final := by
  obtain ⟨chosen, actual, coherent, _retained, _same⟩ :=
    SourceCurrentConjunctionSharedWorkerOutcomeMemos.call_memos p h budget memo query before ready available memos valid
  have same := call_unique reads actual
  rw [same]
  exact coherent

end MicroCFTA.SourceCurrentSharedCallReadValidity
