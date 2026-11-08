import MicroCFTA.SourceCurrentConjunctionTupleAdmission
import MicroCFTA.SourceCurrentConjunctionTuplePullTotal

/-!
# Admission through actual tuple demand

The total cursor samples matching raw tuples before equality work.
Overflow returns its actual sampled state without forcing the continuation.
A fitting positive sample executes the existing tuple worker on that sample.
The result type is shared with the historical eager admission worker.
The later requirement-row fold remains eager.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandAdmission
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionTupleAdmission (Result)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Sample actual demand before processing fitting raw tuples. -/
noncomputable def run (p h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (Result Symbol Formula) :=
  (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).bind fun sampled middle =>
    match sampled with
    | .overflow _ _ => .done .overflow middle
    | .fit [] => .done .zero middle
    | .fit (first :: rest) =>
        (SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) middle).bind fun rows after =>
          .done (.positive rest.length rows) after

/-- Sampling failure retains its exact fault and returned physical state. -/
theorem run_sample_failed (p h budget : Nat) (nodes : List Node)
    (before after : Physical Symbol Formula) (fault : SourceCurrentConjunctionRowsWorker.Fault)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .failed fault after) :
    run p h budget nodes before = .failed fault after := by
  simp only [run, actual, Outcome.bind]

/-- Overflow returns the sampled state without a requirement-row call. -/
theorem run_overflow (p h budget : Nat) (nodes : List Node)
    (before middle : Physical Symbol Formula) (tuples : List (List Edge))
    (cursor : SourceCurrentConjunctionTuplePull.Cursor Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before =
      .done (.overflow tuples cursor) middle) :
    run p h budget nodes before = .done .overflow middle := by
  simp only [run, actual, Outcome.bind]

/-- A complete empty sample returns zero charge at its actual state. -/
theorem run_zero (p h budget : Nat) (nodes : List Node)
    (before middle : Physical Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.fit []) middle) :
    run p h budget nodes before = .done .zero middle := by
  simp only [run, actual, Outcome.bind]

/-- Positive admission retains the actual sampled tuples and ordered tuple allocation. -/
theorem run_positive (p h budget : Nat) (nodes : List Node)
    (before middle after : Physical Symbol Formula) (first : List Edge) (rest : List (List Edge))
    (rows : List (List (List Node)))
    (sampled : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before =
      .done (.fit (first :: rest)) middle)
    (processed : SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) middle = .done rows after) :
    run p h budget nodes before = .done (.positive rest.length rows) after := by
  simp only [run, sampled, Outcome.bind, processed]

/-- A successful positive result supplies its actual demand sample and tuple allocation. -/
theorem positive_sample (p h budget : Nat) (nodes : List Node)
    (before after : Physical Symbol Formula) (predecessor : Nat) (rows : List (List (List Node)))
    (actual : run p h budget nodes before = .done (.positive predecessor rows) after) :
    ∃ first rest middle,
      SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before =
        .done (.fit (first :: rest)) middle ∧
      rest.length = predecessor ∧ rest.length + 1 ≤ budget ∧
      SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) middle = .done rows after := by
  cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before with
  | failed fault middle =>
      simp only [run, sampled, Outcome.bind] at actual
      cases actual
  | done result middle =>
      cases result with
      | overflow tuples cursor =>
          simp only [run, sampled, Outcome.bind] at actual
          cases actual
      | fit tuples =>
          cases tuples with
          | nil =>
              simp only [run, sampled, Outcome.bind] at actual
              cases actual
          | cons first rest =>
              have bound := SourceCurrentConjunctionTuplePullTotal.sample_bounded h budget nodes before middle
                (.fit (first :: rest)) sampled
              simp only [SourceCurrentConjunctionTuplePullTotal.Result.toStatus,
                SourceCurrentConjunctionTuplePullAdmission.Bounded, List.length_cons] at bound
              cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) middle with
              | failed fault final =>
                  simp only [run, sampled, Outcome.bind, processed] at actual
                  cases actual
              | done requirements final =>
                  simp only [run, sampled, Outcome.bind, processed] at actual
                  cases actual
                  exact ⟨first, rest, middle, rfl, rfl, bound, processed⟩

/-- Positive demand admission spends at most the remaining raw tuple budget. -/
theorem positive_charge (p h budget : Nat) (nodes : List Node)
    (before after : Physical Symbol Formula) (predecessor : Nat) (rows : List (List (List Node)))
    (actual : run p h budget nodes before = .done (.positive predecessor rows) after) :
    0 < predecessor + 1 ∧ predecessor + 1 ≤ budget := by
  obtain ⟨_, rest, _, _, count, bound, _⟩ := positive_sample p h budget nodes before after predecessor rows actual
  exact ⟨Nat.zero_lt_succ _, by simpa only [count] using bound⟩

end MicroCFTA.SourceCurrentConjunctionDemandAdmission
