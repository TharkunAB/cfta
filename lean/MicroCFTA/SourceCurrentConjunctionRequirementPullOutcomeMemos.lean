import MicroCFTA.SourceCurrentConjunctionRequirementPullEffects
import MicroCFTA.SourceEqualityProjectionOutcomeGlobalMemos

/-!
# Global memo receipts through every deferred projection outcome

Each pending job retains its literal forest projection and its returned
global tables. A failed projection retains its internal unfolding calls.
Successful prefixes pass their returned tables to that terminal call.
Empty results stop before the unused suffix. Canonicalization adds no
read. Only current forest residency and readiness are required.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementPullOutcomeMemos
open Cache InternedConstructorTemplates
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRowsWorker (Outcome)
open SourceCurrentConjunctionRequirementPull (Cursor Event)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Job" => SourceCurrentConjunctionRowsWorker.Job Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One actual forest projection retains all calls, including its failed prefix. -/
abbrev ProjectionReads (p h : Nat) (job : Job) (before : Physical) (memos saved : Memos) : Prop :=
  SourceEqualityProjectionOutcomeGlobalMemos.ForestReads p h (job.2.map Int.ofNat) job.1 before.heap memos saved

/-- The next cursor event retains the exact actual projection outcome. -/
inductive StepReads (p h : Nat) : Cursor Symbol FullSyntax.Formula → Physical →
    Outcome Symbol FullSyntax.Formula (Event Symbol FullSyntax.Formula) → Memos → Memos → Prop where
  | finished : StepReads p h ⟨[], collected⟩ before
      (.done (.complete (SourceCurrentConjunctionRequirements.canonical collected)) before) memos memos
  | failed (actual : SourceCurrentConjunctionRequirementPull.projection p h job before = .failed fault after)
      (calls : ProjectionReads p h job before memos saved) :
      StepReads p h ⟨job :: rest, collected⟩ before (.failed fault after) memos saved
  | empty (actual : SourceCurrentConjunctionRequirementPull.projection p h job before = .done .empty after)
      (calls : ProjectionReads p h job before memos saved) :
      StepReads p h ⟨job :: rest, collected⟩ before (.done (.complete [.empty]) after) memos saved
  | more (actual : SourceCurrentConjunctionRequirementPull.projection p h job before = .done value after)
      (nonempty : SourceCurrentConjunctionRequirements.isEmpty value = false)
      (calls : ProjectionReads p h job before memos saved) :
      StepReads p h ⟨job :: rest, collected⟩ before
        (.done (.more ⟨rest, collected ++ [value]⟩) after) memos saved

/-- Finite runs retain every successful prefix and their actual terminal failure or result. -/
inductive RunReads (p h : Nat) : Cursor Symbol FullSyntax.Formula → Physical →
    Outcome Symbol FullSyntax.Formula (List Node) → Memos → Memos → Prop where
  | complete (first : StepReads p h cursor before (.done (.complete nodes) after) memos saved) :
      RunReads p h cursor before (.done nodes after) memos saved
  | failed (first : StepReads p h cursor before (.failed fault after) memos saved) :
      RunReads p h cursor before (.failed fault after) memos saved
  | more (first : StepReads p h cursor before (.done (.more next) middle) memos middleMemo)
      (rest : RunReads p h next middle result middleMemo saved) :
      RunReads p h cursor before result memos saved

/-- Every literal singleton projection derives the returned bundle at its exact heap. -/
theorem projection_memos (p h : Nat) (job : Job) (before : Physical) (ready : Ready before)
    (available : Values before.heap job.1) (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, ProjectionReads p h job before memos saved ∧
      Valid (SourceCurrentConjunctionRequirementPull.projection p h job before).state.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  rcases job with ⟨forest, path⟩
  obtain ⟨saved, calls, coherent, retained, same⟩ :=
    SourceEqualityProjectionOutcomeGlobalMemos.forest_memos p h (path.map Int.ofNat) forest before.heap
      ready.semantic ready.costs available memos valid
  refine ⟨saved, calls, ?_, retained, same⟩
  cases actual : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap <;>
    simpa only [SourceCurrentConjunctionRequirementPull.projection,
      SourceCurrentConjunctionRowsWorker.projections, actual, Outcome.bind, Outcome.state,
      SourceEqualityProjectionOutcomePrimitives.reached] using coherent

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem empty_of_test {value : Node}
    (tested : SourceCurrentConjunctionRequirements.isEmpty value = true) : value = .empty := by
  cases value <;> simp_all [SourceCurrentConjunctionRequirements.isEmpty]

/-- Actual cursor steps derive ordered receipts on all results and faults. -/
theorem step_memos (p h : Nat) (cursor : Cursor Symbol FullSyntax.Formula) (before : Physical)
    (ready : Ready before) (available : ∀ job ∈ cursor.pending, Values before.heap job.1)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, StepReads p h cursor before (SourceCurrentConjunctionRequirementPull.step p h cursor before) memos saved ∧
      Valid (SourceCurrentConjunctionRequirementPull.step p h cursor before).state.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  rcases cursor with ⟨jobs, collected⟩
  cases jobs with
  | nil => exact ⟨memos, .finished, valid, extends_refl _, rfl⟩
  | cons job rest =>
      obtain ⟨saved, calls, coherent, retained, same⟩ :=
        projection_memos p h job before ready (available job List.mem_cons_self) memos valid
      cases actual : SourceCurrentConjunctionRequirementPull.projection p h job before with
      | failed fault after =>
          rw [SourceCurrentConjunctionRequirementPull.step_failed p h job rest collected before after fault actual]
          exact ⟨saved, .failed actual calls, by simpa only [actual, Outcome.state] using coherent, retained, same⟩
      | done value after =>
          have finalValid : Valid after.heap saved := by simpa only [actual, Outcome.state] using coherent
          cases tested : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              have empty := empty_of_test tested
              subst value
              rw [SourceCurrentConjunctionRequirementPull.step_empty p h job rest collected before after actual]
              exact ⟨saved, .empty actual calls, finalValid, retained, same⟩
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.step_more p h job rest collected before after value actual tested]
              exact ⟨saved, .more actual tested calls, finalValid, retained, same⟩

private theorem collect_memos (p h : Nat) :
    ∀ (jobs : List Job) (collected : List Node) (before : Physical), Ready before →
      (∀ job ∈ jobs, Values before.heap job.1) → ∀ memos : Memos, Valid before.heap memos →
      ∃ saved, RunReads p h ⟨jobs, collected⟩ before
          (SourceCurrentConjunctionRequirementPull.run p h ⟨jobs, collected⟩ before) memos saved ∧
        Valid (SourceCurrentConjunctionRequirementPull.run p h ⟨jobs, collected⟩ before).state.heap saved ∧
        Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  intro jobs
  induction jobs with
  | nil =>
      intro collected before ready available memos valid
      exact ⟨memos, .complete .finished, valid, extends_refl _, rfl⟩
  | cons job rest ih =>
      intro collected before ready available memos valid
      obtain ⟨middleMemo, first, coherent, retained, same⟩ :=
        projection_memos p h job before ready (available job List.mem_cons_self) memos valid
      cases actual : SourceCurrentConjunctionRequirementPull.projection p h job before with
      | failed fault after =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job rest collected before after fault actual]
          exact ⟨middleMemo, .failed (.failed actual first),
            by simpa only [actual, Outcome.state] using coherent, retained, same⟩
      | done value middle =>
          have middleValid : Valid middle.heap middleMemo := by simpa only [actual, Outcome.state] using coherent
          cases tested : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              have empty := empty_of_test tested
              subst value
              rw [SourceCurrentConjunctionRequirementPull.run_empty p h job rest collected before middle actual]
              exact ⟨middleMemo, .complete (.empty actual first), middleValid, retained, same⟩
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.run_more p h job rest collected before middle value actual tested]
              have kept : Effects before middle := by
                simpa only [actual, Outcome.state] using
                  SourceCurrentConjunctionRequirementPullEffects.projection_effects p h job before ready
                    (available job List.mem_cons_self)
              obtain ⟨saved, later, finalValid, finalRetained, finalSame⟩ :=
                ih (collected ++ [value]) middle kept.ready
                  (fun next member node included => kept.keeps.available node
                    (available next (List.mem_cons_of_mem _ member) node included)) middleMemo middleValid
              exact ⟨saved, .more (.more actual tested first) later, finalValid,
                extends_trans retained finalRetained, finalSame.trans same⟩

/-- Finite cursor demand derives exact final global tables on every actual outcome. -/
theorem run_memos (p h : Nat) (cursor : Cursor Symbol FullSyntax.Formula) (before : Physical)
    (ready : Ready before) (available : ∀ job ∈ cursor.pending, Values before.heap job.1)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, RunReads p h cursor before (SourceCurrentConjunctionRequirementPull.run p h cursor before) memos saved ∧
      Valid (SourceCurrentConjunctionRequirementPull.run p h cursor before).state.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query :=
  collect_memos p h cursor.pending cursor.collected before ready available memos valid

end MicroCFTA.SourceCurrentConjunctionRequirementPullOutcomeMemos
