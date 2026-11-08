import MicroCFTA.SourceCurrentConjunctionRequirementPull

/-!
# Actual requirement projection prefixes

Each read step retains the ordered singleton projection observation.
An Empty result ends the prefix before any remaining job. Faults retain
the stopped cursor and the exact returned physical state. The finite run
producer derives its own graph from the literal executable. Replay uses
the same projection and read bounds. No complete suffix read is assumed.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementPullExecution
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome Job)
open SourceCurrentConjunctionRequirementPull (Cursor Event)
open SourceCurrentConjunctionRequirements (canonical isEmpty)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- A transition records its actual singleton read or its read-free completion. -/
inductive Step (p h : Nat) : Cursor Symbol Formula → Physical Symbol Formula →
    Outcome Symbol Formula (Event Symbol Formula) → Prop where
  | finished : Step p h ⟨[], collected⟩ before (.done (.complete (canonical collected)) before)
  | failed (read : SourceCurrentConjunctionRowsWorker.projections (Symbol := Symbol) (Formula := Formula)
      p h [job] before = .failed fault after) :
      Step p h ⟨job :: rest, collected⟩ before (.failed fault after)
  | empty (read : SourceCurrentConjunctionRowsWorker.projections (Symbol := Symbol) (Formula := Formula)
      p h [job] before = .done [.empty] after) :
      Step p h ⟨job :: rest, collected⟩ before (.done (.complete [.empty]) after)
  | more (read : SourceCurrentConjunctionRowsWorker.projections (Symbol := Symbol) (Formula := Formula)
      p h [job] before = .done [value] after) (nonempty : isEmpty value = false) :
      Step p h ⟨job :: rest, collected⟩ before
        (.done (.more ⟨rest, collected ++ [value]⟩) after)

/-- A prefix retains only the nonterminal transitions before its stopped cursor. -/
inductive Prefix (p h : Nat) : Cursor Symbol Formula → Physical Symbol Formula →
    Cursor Symbol Formula → Physical Symbol Formula → Prop where
  | refl : Prefix p h cursor before cursor before
  | more (first : Step p h cursor before (.done (.more next) middle))
      (rest : Prefix p h next middle stopped stoppedBefore) :
      Prefix p h cursor before stopped stoppedBefore

/-- A finite run records every successful read before its completion or fault. -/
inductive Run (p h : Nat) : Cursor Symbol Formula → Physical Symbol Formula →
    Outcome Symbol Formula (List Node) → Prop where
  | complete (first : Step p h cursor before (.done (.complete nodes) after)) :
      Run p h cursor before (.done nodes after)
  | failed (first : Step p h cursor before (.failed fault after)) :
      Run p h cursor before (.failed fault after)
  | more (first : Step p h cursor before (.done (.more next) middle))
      (rest : Run p h next middle result) : Run p h cursor before result

private theorem singleton_done {p h : Nat} {job : Job Symbol Formula}
    {before after : Physical Symbol Formula} {value : Node}
    (actual : SourceCurrentConjunctionRequirementPull.projection p h job before = .done value after) :
    SourceCurrentConjunctionRowsWorker.projections p h [job] before = .done [value] after := by
  rw [← SourceCurrentConjunctionRequirementPull.projection_singleton, actual]
  rfl

private theorem singleton_failed {p h : Nat} {job : Job Symbol Formula}
    {before after : Physical Symbol Formula} {fault : SourceCurrentConjunctionRowsWorker.Fault}
    (actual : SourceCurrentConjunctionRequirementPull.projection p h job before = .failed fault after) :
    SourceCurrentConjunctionRowsWorker.projections p h [job] before = .failed fault after := by
  rw [← SourceCurrentConjunctionRequirementPull.projection_singleton, actual]
  rfl

omit [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem empty_of_test {value : Node} (actual : isEmpty value = true) : value = .empty := by
  cases value <;> simp_all [isEmpty]

/-- Every transition graph replays its exact physical event or fault. -/
theorem Step.replay {p h : Nat} {cursor : Cursor Symbol Formula} {before : Physical Symbol Formula}
    {result : Outcome Symbol Formula (Event Symbol Formula)} (actual : Step p h cursor before result) :
    SourceCurrentConjunctionRequirementPull.step p h cursor before = result := by
  cases actual with
  | finished => rfl
  | failed read =>
      simp only [SourceCurrentConjunctionRequirementPull.step,
        SourceCurrentConjunctionRequirementPull.projection, read, Outcome.bind]
  | empty read =>
      simp only [SourceCurrentConjunctionRequirementPull.step,
        SourceCurrentConjunctionRequirementPull.projection, read, Outcome.bind, List.headD_cons,
        isEmpty, ite_true]
  | more read nonempty =>
      simp only [SourceCurrentConjunctionRequirementPull.step,
        SourceCurrentConjunctionRequirementPull.projection, read, Outcome.bind, List.headD_cons,
        nonempty, Bool.false_eq_true, ite_false]

/-- A literal transition derives its own ordered observation graph on every outcome. -/
theorem step_graph (p h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula) :
    Step p h cursor before (SourceCurrentConjunctionRequirementPull.step p h cursor before) := by
  rcases cursor with ⟨jobs, collected⟩
  cases jobs with
  | nil =>
      rw [SourceCurrentConjunctionRequirementPull.step_nil]
      exact .finished
  | cons job rest =>
      cases actual : SourceCurrentConjunctionRequirementPull.projection p h job before with
      | failed fault after =>
          rw [SourceCurrentConjunctionRequirementPull.step_failed p h job rest collected before after fault actual]
          exact .failed (singleton_failed actual)
      | done value after =>
          cases tested : isEmpty value with
          | true =>
              have same := empty_of_test tested
              subst value
              rw [SourceCurrentConjunctionRequirementPull.step_empty p h job rest collected before after actual]
              exact .empty (singleton_done actual)
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.step_more p h job rest collected before after value actual tested]
              exact .more (singleton_done actual) tested

/-- Every finite graph replays the complete returned heap, cache, value, and fault. -/
theorem Run.replay {p h : Nat} {cursor : Cursor Symbol Formula} {before : Physical Symbol Formula}
    {result : Outcome Symbol Formula (List Node)} (actual : Run p h cursor before result) :
    SourceCurrentConjunctionRequirementPull.run p h cursor before = result := by
  induction actual with
  | complete first =>
      rw [SourceCurrentConjunctionRequirementPull.run_step, first.replay]
      rfl
  | failed first =>
      rw [SourceCurrentConjunctionRequirementPull.run_step, first.replay]
      rfl
  | more first _ ih =>
      rw [SourceCurrentConjunctionRequirementPull.run_step, first.replay]
      exact ih

/-- The literal finite run derives its own prefix graph without a future read supplier. -/
theorem run_graph (p h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula) :
    Run p h cursor before (SourceCurrentConjunctionRequirementPull.run p h cursor before) := by
  rcases cursor with ⟨jobs, collected⟩
  induction jobs generalizing collected before with
  | nil =>
      rw [SourceCurrentConjunctionRequirementPull.run_nil]
      exact .complete .finished
  | cons job rest ih =>
      cases actual : SourceCurrentConjunctionRequirementPull.projection p h job before with
      | failed fault after =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job rest collected before after fault actual]
          exact .failed (.failed (singleton_failed actual))
      | done value after =>
          cases tested : isEmpty value with
          | true =>
              have same := empty_of_test tested
              subst value
              rw [SourceCurrentConjunctionRequirementPull.run_empty p h job rest collected before after actual]
              exact .complete (.empty (singleton_done actual))
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.run_more p h job rest collected before after value actual tested]
              exact .more (.more (singleton_done actual) tested) (ih (before := after) (collected := collected ++ [value]))

/-- A failed transition exposes the actual next job and its exact failed singleton read. -/
theorem Step.failed_read {p h : Nat} {cursor : Cursor Symbol Formula}
    {before after : Physical Symbol Formula} {fault : SourceCurrentConjunctionRowsWorker.Fault}
    (actual : Step p h cursor before (.failed fault after)) :
    ∃ job rest, cursor.pending = job :: rest ∧
      SourceCurrentConjunctionRowsWorker.projections p h [job] before = .failed fault after := by
  cases actual with
  | failed read => exact ⟨_, _, rfl, read⟩

private theorem failure_prefix_aux {p h : Nat} {cursor : Cursor Symbol Formula}
    {before : Physical Symbol Formula} {result : Outcome Symbol Formula (List Node)}
    (actual : Run p h cursor before result) :
    ∀ fault after, result = .failed fault after →
      ∃ stopped stoppedBefore, Prefix p h cursor before stopped stoppedBefore ∧
        Step p h stopped stoppedBefore (.failed fault after) := by
  induction actual with
  | complete first =>
      intro fault after impossible
      cases impossible
  | failed first =>
      intro fault after same
      cases same
      exact ⟨_, _, .refl, first⟩
  | more first _ ih =>
      intro fault after same
      obtain ⟨stopped, stoppedBefore, earlier, terminal⟩ := ih fault after same
      exact ⟨stopped, stoppedBefore, .more first earlier, terminal⟩

/-- A failed finite graph retains its actual ordered prefix and stopped cursor. -/
theorem Run.failure_prefix {p h : Nat} {cursor : Cursor Symbol Formula}
    {before after : Physical Symbol Formula} {fault : SourceCurrentConjunctionRowsWorker.Fault}
    (actual : Run p h cursor before (.failed fault after)) :
    ∃ stopped stoppedBefore, Prefix p h cursor before stopped stoppedBefore ∧
      Step p h stopped stoppedBefore (.failed fault after) :=
  failure_prefix_aux actual fault after rfl

/-- An observed executable failure derives its own stopped cursor and failed read receipt. -/
theorem run_failed_prefix {p h : Nat} {cursor : Cursor Symbol Formula}
    {before after : Physical Symbol Formula} {fault : SourceCurrentConjunctionRowsWorker.Fault}
    (actual : SourceCurrentConjunctionRequirementPull.run p h cursor before = .failed fault after) :
    ∃ stopped stoppedBefore job rest, Prefix p h cursor before stopped stoppedBefore ∧
      stopped.pending = job :: rest ∧
      SourceCurrentConjunctionRowsWorker.projections p h [job] stoppedBefore = .failed fault after := by
  have graph : Run p h cursor before (.failed fault after) := by
    simpa only [actual] using run_graph p h cursor before
  obtain ⟨stopped, stoppedBefore, earlier, terminal⟩ := graph.failure_prefix
  obtain ⟨job, rest, pending, read⟩ := terminal.failed_read
  exact ⟨stopped, stoppedBefore, job, rest, earlier, pending, read⟩

end MicroCFTA.SourceCurrentConjunctionRequirementPullExecution
