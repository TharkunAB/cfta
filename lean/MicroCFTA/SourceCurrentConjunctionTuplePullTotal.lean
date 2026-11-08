import MicroCFTA.SourceCurrentConjunctionTuplePullProgress
import MicroCFTA.SourceCurrentConjunctionTuplePullAdmission

/-!
# Total physical tuple sampling

Cursor accessibility removes the transition allowance. The sampler returns
fit, overflow with its unforced continuation, or the existing exposure fault.
The operand read allowance is unchanged. This proof does not bound native
runtime work or execute the later requirement-row fold.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullTotal
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome Fault)
open SourceCurrentConjunctionTuplePull (Cursor Event)
open SourceCurrentConjunctionTuplePullProgress (Next wellFounded step_next)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Status" => SourceCurrentConjunctionTuplePullAdmission.Status

/-- Total sampling has no suspended result. Overflow retains its exact continuation. -/
inductive Result (Symbol Formula : Type) where
  | fit (tuples : List (List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))))
  | overflow (tuples : List (List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))))
      (unforced : Cursor Symbol Formula)

/-- Embed a terminal sample in the finite observation API. -/
def Result.toStatus : Result Symbol Formula → Status Symbol Formula
  | .fit tuples => .fit tuples
  | .overflow tuples next => .overflow tuples next

/-- Retain the exact fault and physical state when comparing observations. -/
def observe : Outcome Symbol Formula (Result Symbol Formula) → Outcome Symbol Formula (Status Symbol Formula)
  | .done result after => .done result.toStatus after
  | .failed fault after => .failed fault after

/-- The embedding retains the physical state. -/
theorem observe_state (outcome : Outcome Symbol Formula (Result Symbol Formula)) :
    (observe outcome).state = outcome.state := by cases outcome <;> rfl

private theorem observe_injective : Function.Injective (@observe Symbol Formula) := by
  intro left right same
  cases left with
  | failed fault after =>
      cases right with
      | failed other finish => cases same; rfl
      | done result finish => cases same
  | done result after =>
      cases right with
      | failed fault finish => cases same
      | done other finish =>
          cases result <;> cases other <;> cases same <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private def runBody (h budget : Nat) (cursor : Cursor Symbol Formula)
    (recur : (next : Cursor Symbol Formula) → Next next cursor → List (List Edge) →
      Physical Symbol Formula → Outcome Symbol Formula (Result Symbol Formula))
    (collected : List (List Edge)) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (Result Symbol Formula) :=
  match actual : SourceCurrentConjunctionTuplePull.step h cursor before with
  | .failed fault after => .failed fault after
  | .done (.more next) after =>
      recur next (step_next h cursor before after (.more next) actual) collected after
  | .done (.yield tuple next) after =>
      let sampled := collected ++ [tuple]
      if budget < sampled.length then .done (.overflow sampled next) after
      else recur next (step_next h cursor before after (.yield tuple next) actual) sampled after
  | .done .ended after => .done (.fit collected) after

/-- Run the actual cursor until its first terminal sample or exposure fault. -/
def run (h budget : Nat) : Cursor Symbol Formula → List (List Edge) →
    Physical Symbol Formula → Outcome Symbol Formula (Result Symbol Formula) :=
  WellFounded.fix (C := fun _ : Cursor Symbol Formula => List (List Edge) →
    Physical Symbol Formula → Outcome Symbol Formula (Result Symbol Formula)) wellFounded (runBody h budget)

/-- The total sampler executes the same next transition and the same cap test. -/
theorem run_eq (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) :
    run h budget cursor collected before =
      match SourceCurrentConjunctionTuplePull.step h cursor before with
      | .failed fault after => .failed fault after
      | .done (.more next) after => run h budget next collected after
      | .done (.yield tuple next) after =>
          let sampled := collected ++ [tuple]
          if budget < sampled.length then .done (.overflow sampled next) after
          else run h budget next sampled after
      | .done .ended after => .done (.fit collected) after := by
  change (WellFounded.fix wellFounded (runBody h budget) cursor) collected before = _
  rw [WellFounded.fix_eq]
  change runBody h budget cursor (fun next _ => run h budget next) collected before = _
  unfold runBody
  split <;> simp_all only [] <;> rfl

/-- Start the literal source fold without a transition-count input. -/
def sample (h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (Result Symbol Formula) :=
  run h budget (SourceCurrentConjunctionTuplePull.start nodes) [] before

/-- Some finite observation and every longer observation give this exact total result. -/
theorem run_observation (h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula) :
    ∃ steps, ∀ extra,
      SourceCurrentConjunctionTuplePullAdmission.drive (steps + extra) h budget cursor collected before =
        observe (run h budget cursor collected before) := by
  induction cursor using wellFounded.induction generalizing collected before with
  | h cursor ih =>
      cases actual : SourceCurrentConjunctionTuplePull.step h cursor before with
      | failed fault after =>
          refine ⟨1, ?_⟩
          intro extra
          rw [run_eq, actual]
          rw [show 1 + extra = extra + 1 from by omega]
          simp only [SourceCurrentConjunctionTuplePullAdmission.drive,
            SourceCurrentConjunctionTuplePullAdmission.advance, actual, Outcome.bind, observe]
      | done event after =>
          cases event with
          | ended =>
              refine ⟨1, ?_⟩
              intro extra
              rw [run_eq, actual]
              rw [show 1 + extra = extra + 1 from by omega]
              simp only [SourceCurrentConjunctionTuplePullAdmission.drive,
                SourceCurrentConjunctionTuplePullAdmission.advance, actual, Outcome.bind, observe, Result.toStatus]
          | more next =>
              obtain ⟨steps, eventual⟩ := ih next (step_next h cursor before after (.more next) actual) collected after
              refine ⟨steps + 1, ?_⟩
              intro extra
              rw [run_eq, actual]
              rw [show steps + 1 + extra = (steps + extra) + 1 from by omega]
              simpa only [SourceCurrentConjunctionTuplePullAdmission.drive,
                SourceCurrentConjunctionTuplePullAdmission.advance, actual, Outcome.bind] using eventual extra
          | yield tuple next =>
              by_cases full : budget < (collected ++ [tuple]).length
              · refine ⟨1, ?_⟩
                intro extra
                rw [run_eq, actual]
                rw [show 1 + extra = extra + 1 from by omega]
                simp only [SourceCurrentConjunctionTuplePullAdmission.drive,
                  SourceCurrentConjunctionTuplePullAdmission.advance, actual, Outcome.bind,
                  full, ite_true, observe, Result.toStatus]
              · obtain ⟨steps, eventual⟩ := ih next
                  (step_next h cursor before after (.yield tuple next) actual) (collected ++ [tuple]) after
                refine ⟨steps + 1, ?_⟩
                intro extra
                rw [run_eq, actual]
                rw [show steps + 1 + extra = (steps + extra) + 1 from by omega]
                simpa only [SourceCurrentConjunctionTuplePullAdmission.drive,
                  SourceCurrentConjunctionTuplePullAdmission.advance, actual, Outcome.bind,
                  full, ite_false] using eventual extra

private def Finished : Outcome Symbol Formula (Status Symbol Formula) → Prop
  | .done (.running _ _) _ => False
  | _ => True

private theorem drive_stable (steps extra h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula)
    (finished : Finished (SourceCurrentConjunctionTuplePullAdmission.drive steps h budget cursor collected before)) :
    SourceCurrentConjunctionTuplePullAdmission.drive (steps + extra) h budget cursor collected before =
      SourceCurrentConjunctionTuplePullAdmission.drive steps h budget cursor collected before := by
  induction steps generalizing cursor collected before with
  | zero => cases finished
  | succ steps ih =>
      rw [show steps + 1 + extra = (steps + extra) + 1 from by omega]
      cases first : SourceCurrentConjunctionTuplePullAdmission.advance h budget cursor collected before with
      | failed fault after =>
          simp only [SourceCurrentConjunctionTuplePullAdmission.drive, first, Outcome.bind]
      | done status after =>
          cases status with
          | fit tuples =>
              simp only [SourceCurrentConjunctionTuplePullAdmission.drive, first, Outcome.bind]
          | overflow tuples next =>
              simp only [SourceCurrentConjunctionTuplePullAdmission.drive, first, Outcome.bind]
          | running next sampled =>
              simp only [SourceCurrentConjunctionTuplePullAdmission.drive, first, Outcome.bind] at finished ⊢
              exact ih next sampled after finished

/-- Every terminal finite observation equals the total result at the same reached state. -/
theorem run_of_observation (steps h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula)
    (outcome : Outcome Symbol Formula (Result Symbol Formula))
    (actual : SourceCurrentConjunctionTuplePullAdmission.drive steps h budget cursor collected before = observe outcome) :
    run h budget cursor collected before = outcome := by
  have finished : Finished (SourceCurrentConjunctionTuplePullAdmission.drive steps h budget cursor collected before) := by
    rw [actual]
    cases outcome with
    | failed fault after => trivial
    | done result after => cases result <;> trivial
  obtain ⟨count, eventual⟩ := run_observation h budget cursor collected before
  have stable := (drive_stable steps count h budget cursor collected before finished).trans actual
  have same := (eventual steps).symm.trans (by simpa only [Nat.add_comm] using stable)
  exact observe_injective same

/-- The source sample has an exact finite observation, stable under every larger allowance. -/
theorem sample_observation (h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula) :
    ∃ steps, ∀ extra,
      SourceCurrentConjunctionTuplePullAdmission.sample (steps + extra) h budget nodes before =
        observe (sample h budget nodes before) :=
  run_observation h budget (SourceCurrentConjunctionTuplePull.start nodes) [] before

/-- Total sampling retains the original equality cache on success and failure. -/
theorem run_equality (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) :
    (run h budget cursor collected before).state.equality = before.equality := by
  obtain ⟨steps, eventual⟩ := run_observation h budget cursor collected before
  have actual := eventual 0
  simp only [Nat.add_zero] at actual
  have same := SourceCurrentConjunctionTuplePullAdmission.drive_equality steps h budget cursor collected before
  rw [actual, observe_state] at same
  exact same

/-- A fitting result respects the budget. Overflow contains exactly one extra raw tuple. -/
theorem sample_bounded (h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (result : Result Symbol Formula) (actual : sample h budget nodes before = .done result after) :
    SourceCurrentConjunctionTuplePullAdmission.Bounded budget result.toStatus := by
  obtain ⟨steps, eventual⟩ := sample_observation h budget nodes before
  have observed := eventual 0
  simp only [Nat.add_zero, actual, observe] at observed
  exact SourceCurrentConjunctionTuplePullAdmission.sample_bounded steps h budget nodes before after result.toStatus observed

/-- A reached exposure fault propagates with its exact physical state. -/
theorem run_failed (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before after : Physical Symbol Formula) (fault : Fault)
    (actual : SourceCurrentConjunctionTuplePull.step h cursor before = .failed fault after) :
    run h budget cursor collected before = .failed fault after := by rw [run_eq, actual]

/-- Overflow returns the yielded continuation without a further call on it. -/
theorem run_overflow (h budget : Nat) (cursor next : Cursor Symbol Formula) (collected : List (List Edge))
    (tuple : List Edge) (before after : Physical Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePull.step h cursor before = .done (.yield tuple next) after)
    (full : budget < (collected ++ [tuple]).length) :
    run h budget cursor collected before = .done (.overflow (collected ++ [tuple]) next) after := by
  rw [run_eq, actual]
  simp only [full, ite_true]

end MicroCFTA.SourceCurrentConjunctionTuplePullTotal
