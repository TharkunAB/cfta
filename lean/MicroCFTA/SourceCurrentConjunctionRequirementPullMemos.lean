import MicroCFTA.SourceCurrentConjunctionRequirementPullExecution
import MicroCFTA.SourceCurrentConjunctionRequirementPullEffects
import MicroCFTA.SourceCurrentConjunctionRowsWorkerActual
import MicroCFTA.SourceCurrentConjunctionGlobalMemos

/-!
# Ordered memo receipts for deferred requirement projections

Each completed step records its actual singleton projection. Repeated
jobs remain separate calls. The first Empty result stops the receipt.
Only the current pending forests need resident closed operands.

These laws cover successful steps and runs. A failed projection can make
internal unfolding calls before it fails. The existing projection memo
graphs do not record those partial calls. This module does not classify
that failure as a step without reads or supply its final memo bundle.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementPullMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRequirementPull (Cursor Event)
open SourceCurrentConjunctionRowsWorker (Outcome)
open SourceCurrentConjunctionCompletionReads (Inputs Projections)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Job" => SourceCurrentConjunctionRowsWorker.Job Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One actual singleton observation retains all of its ordered global calls. -/
def ProjectionReads {p h : Nat} {job : Job} {before after : Physical} {value : Node}
    (_actual : SourceCurrentConjunctionRowsWorker.projections p h [job] before = .done [value] after)
    (memos saved : Memos) : Prop :=
  ∃ trace : Projections [job] before.heap [value] after.heap,
    SourceCurrentConjunctionGlobalMemos.ProjectionsReads trace memos saved

/-- A completed cursor transition adds no call after its sole actual projection. -/
inductive StepReads (p h : Nat) : Cursor Symbol FullSyntax.Formula → Physical →
    Event Symbol FullSyntax.Formula → Physical → Memos → Memos → Prop where
  | finished : StepReads p h ⟨[], collected⟩ before
      (.complete (SourceCurrentConjunctionRequirements.canonical collected)) before memos memos
  | empty (read : SourceCurrentConjunctionRowsWorker.projections p h [job] before = .done [.empty] after)
      (calls : ProjectionReads read memos saved) :
      StepReads p h ⟨job :: rest, collected⟩ before (.complete [.empty]) after memos saved
  | more (read : SourceCurrentConjunctionRowsWorker.projections p h [job] before = .done [value] after)
      (nonempty : SourceCurrentConjunctionRequirements.isEmpty value = false)
      (calls : ProjectionReads read memos saved) :
      StepReads p h ⟨job :: rest, collected⟩ before
        (.more ⟨rest, collected ++ [value]⟩) after memos saved

/-- A complete run passes each returned bundle to the next actual step. -/
inductive RunReads (p h : Nat) : Cursor Symbol FullSyntax.Formula → Physical →
    List Node → Physical → Memos → Memos → Prop where
  | complete (first : StepReads p h cursor before (.complete nodes) after memos saved) :
      RunReads p h cursor before nodes after memos saved
  | more (first : StepReads p h cursor before (.more next) middle memos middleMemo)
      (rest : RunReads p h next middle nodes after middleMemo saved) :
      RunReads p h cursor before nodes after memos saved

/-- A supplied transition receipt fixes its exact physical event and endpoint. -/
theorem StepReads.replay {p h : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {before after : Physical} {event : Event Symbol FullSyntax.Formula} {memos saved : Memos}
    (reads : StepReads p h cursor before event after memos saved) :
    SourceCurrentConjunctionRequirementPull.step p h cursor before = .done event after := by
  cases reads with
  | finished => rfl
  | empty read _ => exact SourceCurrentConjunctionRequirementPullExecution.Step.replay (.empty read)
  | more read nonempty _ => exact SourceCurrentConjunctionRequirementPullExecution.Step.replay (.more read nonempty)

/-- A supplied run receipt fixes the complete returned value and physical state. -/
theorem RunReads.replay {p h : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {before after : Physical} {nodes : List Node} {memos saved : Memos}
    (reads : RunReads p h cursor before nodes after memos saved) :
    SourceCurrentConjunctionRequirementPull.run p h cursor before = .done nodes after := by
  induction reads with
  | complete first =>
      rw [SourceCurrentConjunctionRequirementPull.run_step, first.replay]
      rfl
  | more first _ ih =>
      rw [SourceCurrentConjunctionRequirementPull.run_step, first.replay]
      exact ih

/-- The actual completed singleton derives its own exact coherent memo bundle. -/
theorem projection_memos {p h : Nat} {job : Job} {before after : Physical} {value : Node}
    (actual : SourceCurrentConjunctionRowsWorker.projections p h [job] before = .done [value] after)
    (ready : Ready before) (available : Values before.heap job.1) (closed : ClosedValues job.1)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, ProjectionReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  have trace := (SourceCurrentConjunctionRowsWorkerActual.projections_graph actual).1
  obtain ⟨saved, calls, coherent, retained, same⟩ :=
    SourceCurrentConjunctionGlobalMemos.projections_memos trace ready.semantic ready.costs
      (by intro next member; cases List.mem_singleton.mp member; exact ⟨available, closed⟩) memos valid
  exact ⟨saved, ⟨trace, calls⟩, coherent, retained, same⟩

/-- A literal successful step derives only the singleton calls it actually performed. -/
theorem step_memos {p h : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {before after : Physical} {event : Event Symbol FullSyntax.Formula}
    (actual : SourceCurrentConjunctionRequirementPull.step p h cursor before = .done event after)
    (ready : Ready before) (inputs : Inputs before.heap cursor.pending)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, StepReads p h cursor before event after memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  have graph : SourceCurrentConjunctionRequirementPullExecution.Step p h cursor before (.done event after) := by
    simpa only [actual] using SourceCurrentConjunctionRequirementPullExecution.step_graph p h cursor before
  cases graph with
  | finished => exact ⟨memos, .finished, valid, extends_refl _, rfl⟩
  | empty read =>
      have own := inputs _ List.mem_cons_self
      obtain ⟨saved, calls, coherent, retained, same⟩ := projection_memos read ready own.1 own.2 memos valid
      exact ⟨saved, .empty read calls, coherent, retained, same⟩
  | more read nonempty =>
      have own := inputs _ List.mem_cons_self
      obtain ⟨saved, calls, coherent, retained, same⟩ := projection_memos read ready own.1 own.2 memos valid
      exact ⟨saved, .more read nonempty calls, coherent, retained, same⟩

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem empty_of_test {value : Node}
    (tested : SourceCurrentConjunctionRequirements.isEmpty value = true) : value = .empty := by
  cases value <;> simp_all [SourceCurrentConjunctionRequirements.isEmpty]

/-- Successful finite demand derives every intermediate memo premise from actual effects. -/
theorem run_memos {p h : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {before after : Physical} {nodes : List Node}
    (actual : SourceCurrentConjunctionRequirementPull.run p h cursor before = .done nodes after)
    (ready : Ready before) (inputs : Inputs before.heap cursor.pending)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, RunReads p h cursor before nodes after memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  rcases cursor with ⟨jobs, collected⟩
  change Inputs before.heap jobs at inputs
  change SourceCurrentConjunctionRequirementPull.run p h ⟨jobs, collected⟩ before = .done nodes after at actual
  revert actual
  revert valid
  revert memos
  revert inputs
  revert ready
  induction jobs generalizing collected before after nodes with
  | nil =>
      intro ready inputs memos valid actual
      rw [SourceCurrentConjunctionRequirementPull.run_nil] at actual
      cases actual
      exact ⟨memos, .complete .finished, valid, extends_refl _, rfl⟩
  | cons job rest ih =>
      intro ready inputs memos valid actual
      have own := inputs job List.mem_cons_self
      cases projected : SourceCurrentConjunctionRequirementPull.projection p h job before with
      | failed fault middle =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job rest collected before middle fault projected] at actual
          cases actual
      | done value middle =>
          have singleton : SourceCurrentConjunctionRowsWorker.projections p h [job] before = .done [value] middle := by
            rw [← SourceCurrentConjunctionRequirementPull.projection_singleton, projected]
            rfl
          obtain ⟨middleMemo, first, coherent, retained, same⟩ :=
            projection_memos singleton ready own.1 own.2 memos valid
          cases tested : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              have empty := empty_of_test tested
              subst value
              rw [SourceCurrentConjunctionRequirementPull.run_empty p h job rest collected before middle projected] at actual
              cases actual
              exact ⟨middleMemo, .complete (.empty singleton first), coherent, retained, same⟩
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.run_more p h job rest collected before middle value projected tested] at actual
              have kept : Effects before middle := by
                simpa only [projected, Outcome.state] using
                  SourceCurrentConjunctionRequirementPullEffects.projection_effects p h job before ready own.1
              have remaining : Inputs middle.heap rest :=
                SourceCurrentConjunctionCompletionReads.Inputs.keeps
                  (fun next member => inputs next (List.mem_cons_of_mem _ member)) kept.keeps
              obtain ⟨saved, later, finalValid, finalRetained, finalSame⟩ :=
                ih (collected := collected ++ [value]) (before := middle) (after := after)
                  (nodes := nodes) kept.ready remaining middleMemo coherent actual
              exact ⟨saved, .more (.more singleton tested first) later, finalValid,
                extends_trans retained finalRetained, finalSame.trans same⟩

end MicroCFTA.SourceCurrentConjunctionRequirementPullMemos
