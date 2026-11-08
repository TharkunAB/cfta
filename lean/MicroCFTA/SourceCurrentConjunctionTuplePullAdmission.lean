import MicroCFTA.SourceCurrentConjunctionTuplePull

/-!
# Bounded observation of suspended raw tuple sampling

The sampler stops at the first `budget + 1` matching raw tuples. It does
not step the returned overflow continuation. End of stream establishes a
fitting complete sample. Exposure faults retain their actual physical state.
The equality cache is unchanged on every outcome.

The observation allowance counts transitions of this explicit machine.
Its end suspends the sampler. It is not a native error or a proved runtime
bound. This module does not execute equality folds or requirement rows.
Their later lazy demand and shared publication remain open. The selected
executor has not yet been changed to use this sampler.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullAdmission
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome Fault)
open SourceCurrentConjunctionTuplePull (Cursor Event)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- A finite observation retains the cursor whenever sampling can continue. -/
inductive Status (Symbol Formula : Type) where
  | running (cursor : Cursor Symbol Formula)
      (collected : List (List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))))
  | fit (tuples : List (List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))))
  | overflow (tuples : List (List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))))
      (unforced : Cursor Symbol Formula)

/-- Fitting and suspended samples respect the budget; overflow has exactly one extra tuple. -/
def Bounded (budget : Nat) : Status Symbol Formula → Prop
  | .running _ tuples | .fit tuples => tuples.length ≤ budget
  | .overflow tuples _ => tuples.length = budget + 1

private def OutcomeBounded (budget : Nat) : Outcome Symbol Formula (Status Symbol Formula) → Prop
  | .done status _ => Bounded budget status
  | .failed _ _ => True

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Observe one actual cursor transition and test the cap only after a yield. -/
def advance (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) : Outcome Symbol Formula (Status Symbol Formula) :=
  (SourceCurrentConjunctionTuplePull.step h cursor before).bind fun event after => match event with
    | .more next => .done (.running next collected) after
    | .yield tuple next =>
        let sampled := collected ++ [tuple]
        if budget < sampled.length then .done (.overflow sampled next) after
        else .done (.running next sampled) after
    | .ended => .done (.fit collected) after

/-- Observe finitely many transitions. A depleted allowance leaves a resumable status. -/
def drive : Nat → Nat → Nat → Cursor Symbol Formula → List (List Edge) →
    Physical Symbol Formula → Outcome Symbol Formula (Status Symbol Formula)
  | 0, _, _, cursor, collected, before => .done (.running cursor collected) before
  | steps + 1, h, budget, cursor, collected, before =>
      (advance h budget cursor collected before).bind fun status after => match status with
        | .running next sampled => drive steps h budget next sampled after
        | .fit sampled => .done (.fit sampled) after
        | .overflow sampled next => .done (.overflow sampled next) after

/-- Start sampling the literal source fold without a supplied edge-list oracle. -/
def sample (steps h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (Status Symbol Formula) :=
  drive steps h budget (SourceCurrentConjunctionTuplePull.start nodes) [] before

/-- Cursor faults propagate before any further sample or continuation demand. -/
theorem advance_failed (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before after : Physical Symbol Formula) (fault : Fault)
    (actual : SourceCurrentConjunctionTuplePull.step h cursor before = .failed fault after) :
    advance h budget cursor collected before = .failed fault after := by
  simp only [advance, actual, Outcome.bind]

/-- End of the actual stream returns the complete sample at the actual reached state. -/
theorem advance_end (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before after : Physical Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePull.step h cursor before = .done .ended after) :
    advance h budget cursor collected before = .done (.fit collected) after := by
  simp only [advance, actual, Outcome.bind]

/-- The extra matching tuple stops sampling without a call on its continuation. -/
theorem advance_overflow (h budget : Nat) (cursor next : Cursor Symbol Formula)
    (collected : List (List Edge)) (tuple : List Edge) (before after : Physical Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePull.step h cursor before = .done (.yield tuple next) after)
    (full : collected.length = budget) :
    advance h budget cursor collected before = .done (.overflow (collected ++ [tuple]) next) after := by
  simp only [advance, actual, Outcome.bind, List.length_append, List.length_singleton, full]
  simp only [Nat.lt_succ_self, ite_true]

/-- Once overflow occurs, any observation allowance returns it without another pull. -/
theorem drive_overflow (steps h budget : Nat) (cursor next : Cursor Symbol Formula)
    (collected sampled : List (List Edge)) (before after : Physical Symbol Formula)
    (actual : advance h budget cursor collected before = .done (.overflow sampled next) after) :
    drive (steps + 1) h budget cursor collected before = .done (.overflow sampled next) after := by
  simp only [drive, actual, Outcome.bind]

/-- The observation limit is suspension with the exact unchanged cursor and state. -/
theorem drive_zero (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) :
    drive 0 h budget cursor collected before = .done (.running cursor collected) before := rfl

private theorem advance_bounded (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) (bound : collected.length ≤ budget) :
    OutcomeBounded budget (advance h budget cursor collected before) := by
  cases actual : SourceCurrentConjunctionTuplePull.step h cursor before with
  | failed fault after => simp only [advance, actual, Outcome.bind, OutcomeBounded]
  | done event after =>
      cases event with
      | more next => simpa only [advance, actual, Outcome.bind, OutcomeBounded, Bounded] using bound
      | ended => simpa only [advance, actual, Outcome.bind, OutcomeBounded, Bounded] using bound
      | yield tuple next =>
          simp only [advance, actual, Outcome.bind]
          split <;> simp only [OutcomeBounded, Bounded, List.length_append, List.length_singleton] at * <;> omega

private theorem drive_bounded (steps h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) (bound : collected.length ≤ budget) :
    OutcomeBounded budget (drive steps h budget cursor collected before) := by
  induction steps generalizing cursor collected before with
  | zero => exact bound
  | succ steps ih =>
      have first := advance_bounded h budget cursor collected before bound
      cases actual : advance h budget cursor collected before with
      | failed fault after => simp only [drive, actual, Outcome.bind, OutcomeBounded]
      | done status after =>
          rw [actual] at first
          cases status with
          | running next sampled =>
              simpa only [drive, actual, Outcome.bind] using ih next sampled after first
          | fit sampled => simpa only [drive, actual, Outcome.bind] using first
          | overflow sampled next => simpa only [drive, actual, Outcome.bind] using first

/-- Every actual sampled return has the fitting bound or the exact extra-tuple charge. -/
theorem sample_bounded (steps h budget : Nat) (nodes : List Node)
    (before after : Physical Symbol Formula) (status : Status Symbol Formula)
    (actual : sample steps h budget nodes before = .done status after) : Bounded budget status := by
  have bounded := drive_bounded steps h budget (SourceCurrentConjunctionTuplePull.start nodes) [] before (by simp)
  change OutcomeBounded budget (sample steps h budget nodes before) at bounded
  simpa only [actual, OutcomeBounded] using bounded

/-- Counting and matching do not modify equality allocations, including on failures. -/
theorem advance_equality (h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) :
    (advance h budget cursor collected before).state.equality = before.equality := by
  have same := SourceCurrentConjunctionTuplePull.step_equality h cursor before
  cases actual : SourceCurrentConjunctionTuplePull.step h cursor before with
  | failed fault after => simpa only [advance, actual, Outcome.bind, Outcome.state] using same
  | done event after =>
      cases event with
      | more next => simpa only [advance, actual, Outcome.bind, Outcome.state] using same
      | ended => simpa only [advance, actual, Outcome.bind, Outcome.state] using same
      | yield tuple next =>
          simp only [advance, actual, Outcome.bind]
          split <;> simpa only [actual, Outcome.state] using same

/-- A finite observation preserves equality state on success, suspension, and failure. -/
theorem drive_equality (steps h budget : Nat) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) :
    (drive steps h budget cursor collected before).state.equality = before.equality := by
  induction steps generalizing cursor collected before with
  | zero => rfl
  | succ steps ih =>
      have first := advance_equality h budget cursor collected before
      cases actual : advance h budget cursor collected before with
      | failed fault after => simpa only [drive, actual, Outcome.bind, Outcome.state] using first
      | done status after =>
          simp only [actual, Outcome.state] at first
          cases status with
          | running next sampled =>
              simpa only [drive, actual, Outcome.bind] using (ih next sampled after).trans first
          | fit sampled => simpa only [drive, actual, Outcome.bind, Outcome.state] using first
          | overflow sampled next => simpa only [drive, actual, Outcome.bind, Outcome.state] using first

/-- Empty source operands end without an exposure, at every positive observation allowance. -/
theorem sample_empty (steps h budget : Nat) (before : Physical Symbol Formula) :
    sample (steps + 1) h budget [] before = .done (.fit []) before := by
  simp only [sample, SourceCurrentConjunctionTuplePull.start, drive, advance,
    SourceCurrentConjunctionTuplePull.step, Outcome.bind]

end MicroCFTA.SourceCurrentConjunctionTuplePullAdmission
