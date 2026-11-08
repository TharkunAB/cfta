import MicroCFTA.SourceCurrentConjunctionDemandAdmission
import MicroCFTA.SourceCurrentConjunctionRowsWorkerActual
import MicroCFTA.SourceCurrentConjunctionRowsWorkerCompletion
import MicroCFTA.SourceCurrentConjunctionTuplePullShapes
import MicroCFTA.SourceCurrentConjunctionTuplePullStability

/-!
# Actual demand admission graphs

Admission retains the actual total sample and its exact physical state.
Positive admission allocates exactly the fitting sampled tuples. Overflow
and zero return the sampled state without tuple allocation. These graphs
do not assert the historical eager operand exposure schedule.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandExecution
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Tuples)
open SourceCurrentConjunctionRowsWorkerCompletion (StableRun)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- The graph records actual sampling and only the reached tuple allocation. -/
inductive Admission : Nat → List Node → Physical Symbol Formula →
    SourceCurrentConjunctionTupleAdmission.Result Symbol Formula → Physical Symbol Formula → Prop where
  | overflow {h budget : Nat} {nodes : List Node} {before middle : Physical Symbol Formula}
      {tuples : List (List Edge)} {cursor : SourceCurrentConjunctionTuplePull.Cursor Symbol Formula}
      (sampled : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before =
        .done (.overflow tuples cursor) middle) :
      Admission budget nodes before .overflow middle
  | zero {h budget : Nat} {nodes : List Node} {before middle : Physical Symbol Formula}
      (sampled : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.fit []) middle) :
      Admission budget nodes before .zero middle
  | positive {h budget : Nat} {nodes : List Node} {before middle after : Physical Symbol Formula}
      {first : List Edge} {rest : List (List Edge)} {requirements : List (List (List Node))}
      (sampled : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before =
        .done (.fit (first :: rest)) middle)
      (allocated : Tuples (first :: rest) middle requirements after) :
      Admission budget nodes before (.positive rest.length requirements) after

/-- Every successful literal admission derives the same actual sample and tuple graph. -/
theorem admission_graph {p h budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : SourceCurrentConjunctionDemandAdmission.run p h budget nodes before = .done result after) :
    Admission budget nodes before result after := by
  cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before with
  | failed fault middle =>
      simp only [SourceCurrentConjunctionDemandAdmission.run, sampled, Outcome.bind] at actual
      cases actual
  | done selected middle =>
      cases selected with
      | overflow tuples cursor =>
          simp only [SourceCurrentConjunctionDemandAdmission.run, sampled, Outcome.bind] at actual
          cases actual
          exact .overflow sampled
      | fit tuples =>
          cases tuples with
          | nil =>
              simp only [SourceCurrentConjunctionDemandAdmission.run, sampled, Outcome.bind] at actual
              cases actual
              exact .zero sampled
          | cons first rest =>
              cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) middle with
              | failed fault final =>
                  simp only [SourceCurrentConjunctionDemandAdmission.run, sampled, Outcome.bind, processed] at actual
                  cases actual
              | done requirements final =>
                  have shaped := SourceCurrentConjunctionTuplePullShapes.sample_fit h budget nodes before middle
                    (first :: rest) sampled
                  have allocated := SourceCurrentConjunctionRowsWorkerActual.tuples_graph
                    (fun tuple member => SourceCurrentConjunctionRowsAllocation.matching_arity tuple
                      (shaped tuple member).2.1) processed
                  simp only [SourceCurrentConjunctionDemandAdmission.run, sampled, Outcome.bind, processed] at actual
                  cases actual
                  exact .positive sampled allocated

/-- Positive admission charges the full sampled raw count within the remaining budget. -/
theorem Admission.positive_charge {budget predecessor : Nat} {nodes : List Node}
    {before after : Physical Symbol Formula} {requirements : List (List (List Node))}
    (actual : Admission budget nodes before (.positive predecessor requirements) after) :
    0 < predecessor + 1 ∧ predecessor + 1 ≤ budget := by
  cases actual with
  | positive sampled allocated =>
      have bounded := SourceCurrentConjunctionTuplePullTotal.sample_bounded _ _ _ _ _ _ sampled
      simp only [SourceCurrentConjunctionTuplePullTotal.Result.toStatus,
        SourceCurrentConjunctionTuplePullAdmission.Bounded, List.length_cons] at bounded
      exact ⟨Nat.zero_lt_succ _, bounded⟩

private theorem sample_stable {h budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTuplePullTotal.Result Symbol Formula}
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after) :
    ∃ bound, ∀ H, bound ≤ H →
      SourceCurrentConjunctionTuplePullTotal.sample H budget nodes before = .done result after :=
  ⟨h, fun _ enough => SourceCurrentConjunctionTuplePullStability.sample_done_stable actual enough⟩

/-- An actual admission graph replays stably with the same full physical result. -/
theorem admission_complete {budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) :
    StableRun (fun p h => SourceCurrentConjunctionDemandAdmission.run p h budget nodes before) result after := by
  cases actual with
  | overflow sampled =>
      obtain ⟨h, done⟩ := sample_stable sampled
      refine ⟨0, h, ?_⟩
      intro P H _ enough
      simp only [SourceCurrentConjunctionDemandAdmission.run, done H enough, Outcome.bind]
  | zero sampled =>
      obtain ⟨h, done⟩ := sample_stable sampled
      refine ⟨0, h, ?_⟩
      intro P H _ enough
      simp only [SourceCurrentConjunctionDemandAdmission.run, done H enough, Outcome.bind]
  | positive sampled allocated =>
      obtain ⟨h, sampledDone⟩ := sample_stable sampled
      obtain ⟨p, laterH, allocatedDone⟩ := SourceCurrentConjunctionRowsWorkerCompletion.tuples_complete allocated
      refine ⟨p, max h laterH, ?_⟩
      intro P H enoughP enoughH
      simp only [SourceCurrentConjunctionDemandAdmission.run, sampledDone H (by omega), Outcome.bind,
        allocatedDone P H enoughP (by omega)]

end MicroCFTA.SourceCurrentConjunctionDemandExecution
