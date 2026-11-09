import MicroCFTA.SourceCurrentConjunctionSharedWorklistRun
import MicroCFTA.SourceCurrentConjunctionRequirementCellsCompletion
import MicroCFTA.SourceCurrentConjunctionTuplePullStability

/-!
# Successful shared execution at larger observation bounds

Replay retains the exact table, task queue, private cells and physical state.
It follows the actual finite transition graph. It needs no readiness or cost
premise. It does not supply sufficient bounds for a successful execution.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistStability
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistRun (Run)
variable {Symbol Formula : Type}
local notation "Node" => Value Symbol (SourceSymbolicIndex.Constraint Formula)
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- A successful visit retains its complete returned state at every larger read bound. -/
theorem visit_done_stable {h largerH : Nat} {nodes : List Node}
    {rest : List (Task Symbol Formula)} {before after : WorkState} {event : Event}
    (actual : visit h nodes rest before = .done event after) (enoughH : h ≤ largerH) :
    visit largerH nodes rest before = .done event after := by
  cases empty : nodes.any isEmpty with
  | true => simpa only [visit, empty, ite_true] using actual
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
          before.budget (queryTable before.table) nodes with
      | true =>
          simpa only [visit, empty, Bool.false_eq_true, ite_false, skipped, ite_true] using actual
      | false =>
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              simp only [visit, empty, skipped, Bool.false_eq_true, ite_false, sampled] at actual
              cases actual
          | done result physical =>
              have stable := SourceCurrentConjunctionTuplePullStability.sample_done_stable sampled enoughH
              simp only [visit, empty, skipped, Bool.false_eq_true, ite_false, sampled] at actual
              simpa only [visit, empty, skipped, Bool.false_eq_true, ite_false, stable] using actual

/-- A successful task retains the same event and entire state at larger bounds. -/
theorem step_done_stable {p h largerP largerH : Nat} {before after : WorkState} {event : Event}
    (actual : step p h before = .done event after) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    step largerP largerH before = .done event after := by
  cases pending : before.pending with
  | nil => simpa only [step, pending] using actual
  | cons task rest =>
      cases task with
      | nodes nodes =>
          simp only [step, pending] at actual ⊢
          exact visit_done_stable actual enoughH
      | requirements handles =>
          cases handles with
          | nil => simpa only [step, pending] using actual
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle
                  before.storage.requirements with
              | failed fault cells =>
                  simp only [step, pending, forced] at actual
                  cases actual
              | done nodes cells =>
                  have stable := SourceCurrentConjunctionRequirementCellsCompletion.force_done_stable
                    forced enoughP enoughH
                  simp only [step, pending, forced] at actual
                  simpa only [step, pending, stable] using visit_done_stable actual enoughH
      | rows handle => simpa only [step, pending] using actual

private theorem run_unique {p h : Nat} {before : WorkState}
    {first second : Outcome Symbol Formula} (one : Run p h before first)
    (two : Run p h before second) : first = second := by
  induction one generalizing second with
  | failed actual =>
      cases two with
      | failed other => exact actual.symm.trans other
      | drained other => cases actual.symm.trans other
      | more other tail => cases actual.symm.trans other
  | drained actual =>
      cases two with
      | failed other => cases actual.symm.trans other
      | drained other => exact actual.symm.trans other
      | more other tail => cases actual.symm.trans other
  | more actual tail ih =>
      cases two with
      | failed other => cases actual.symm.trans other
      | drained other => cases actual.symm.trans other
      | more other rest =>
          have same := Outcome.done.inj (actual.symm.trans other)
          cases same.2
          exact ih rest

private theorem run_replay {p h largerP largerH : Nat}
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH)
    {before : WorkState} {outcome : Outcome Symbol Formula} (trace : Run p h before outcome) :
    ∀ event after, outcome = .done event after → Run largerP largerH before (.done event after) := by
  induction trace with
  | failed actual => intro event after impossible; cases impossible
  | drained actual =>
      intro event after same
      cases same
      exact Run.drained (step_done_stable actual enoughP enoughH)
  | more actual tail ih =>
      intro event after same
      exact Run.more (step_done_stable actual enoughP enoughH) (ih event after same)

/-- Every successful original exploration replays the same complete private endpoint. -/
theorem explore_done_stable {p h largerP largerH budget : Nat} {start : Node}
    {before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula} {after : WorkState} {event : Event}
    (actual : SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before = .done event after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionSharedWorklistRun.explore largerP largerH budget start before = .done event after := by
  have trace := SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before
  rw [actual] at trace
  exact (run_unique (run_replay enoughP enoughH trace event after rfl)
    (SourceCurrentConjunctionSharedWorklistRun.explore_graph largerP largerH budget start before)).symm

/-- Successful observations at any two bounds identify the same event and full state. -/
theorem explore_done_unique {p h otherP otherH budget : Nat} {start : Node}
    {before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula}
    {after later : WorkState} {first second : Event}
    (one : SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before = .done first after)
    (two : SourceCurrentConjunctionSharedWorklistRun.explore otherP otherH budget start before = .done second later) :
    first = second ∧ after = later := by
  have a := explore_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := explore_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  exact Outcome.done.inj (a.symm.trans b)

end MicroCFTA.SourceCurrentConjunctionSharedWorklistStability
