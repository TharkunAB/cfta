import MicroCFTA.SourceCurrentConjunctionRowsWorker
import MicroCFTA.SourceCurrentConjunctionTupleBudget

/-!
# Physical tuple-budget admission before equality work

The worker exposes the operands once with the existing eager read schedule.
It takes at most budget plus one raw matching tuples. It counts these tuples
before equality rejection or requirement projection. Overflow returns the
exposure state. A zero charge returns no rows at that same state. A fitting
positive charge executes the existing tuple worker in its original order.

The selected conjunction explorer does not use this helper yet. The helper
retains the existing eager exposure boundary. It does not establish Haskell
lazy read demand or a native bound on constructing the tuple product.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleAdmission
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- A positive charge stores its predecessor, so its actual charge is always positive. -/
inductive Result (Symbol Formula : Type) where
  | overflow
  | zero
  | positive (predecessor : Nat)
      (requirements : List (List (List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))))

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Count the capped raw tuples before any equality fold or requirement projection. -/
noncomputable def run (p h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (Result Symbol Formula) :=
  (SourceCurrentConjunctionRowsWorker.exposures h nodes before).bind fun edges exposed =>
    let sampled := SourceCurrentConjunctionTupleBudget.sample budget
      (SourceCurrentConjunctionTuples.tuples edges)
    if budget < sampled.length then .done .overflow exposed
    else match sampled with
      | [] => .done .zero exposed
      | first :: rest =>
          (SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) exposed).bind fun rows after =>
            .done (.positive rest.length rows) after

/-- A failed exposure retains its exact fault and both returned physical states. -/
theorem run_exposures_failed (p h budget : Nat) (nodes : List Node)
    (before after : Physical Symbol Formula) (fault : SourceCurrentConjunctionRowsWorker.Fault)
    (failed : SourceCurrentConjunctionRowsWorker.exposures h nodes before = .failed fault after) :
    run p h budget nodes before = .failed fault after := by
  simp only [run, failed, Outcome.bind]

/-- Overflow skips equality and projection and returns the actual exposure state. -/
theorem run_overflow (p h budget : Nat) (nodes : List Node) (before exposed : Physical Symbol Formula)
    (edges : List (List Edge))
    (read : SourceCurrentConjunctionRowsWorker.exposures h nodes before = .done edges exposed)
    (overflow : budget < (SourceCurrentConjunctionTupleBudget.sample budget
      (SourceCurrentConjunctionTuples.tuples edges)).length) :
    run p h budget nodes before = .done .overflow exposed := by
  simp only [run, read, Outcome.bind, overflow, ↓reduceIte]

/-- A zero raw tuple count returns no rows without equality or projection work. -/
theorem run_zero (p h budget : Nat) (nodes : List Node) (before exposed : Physical Symbol Formula)
    (edges : List (List Edge))
    (read : SourceCurrentConjunctionRowsWorker.exposures h nodes before = .done edges exposed)
    (zero : SourceCurrentConjunctionTupleBudget.sample budget
      (SourceCurrentConjunctionTuples.tuples edges) = []) :
    run p h budget nodes before = .done .zero exposed := by
  simp only [run, read, Outcome.bind, zero, List.length_nil, Nat.not_lt_zero, ↓reduceIte]

/-- A fitting positive sample retains the actual ordered tuple result and returned state. -/
theorem run_positive (p h budget : Nat) (nodes : List Node)
    (before exposed after : Physical Symbol Formula) (edges : List (List Edge))
    (first : List Edge) (rest : List (List Edge)) (rows : List (List (List Node)))
    (read : SourceCurrentConjunctionRowsWorker.exposures h nodes before = .done edges exposed)
    (sampled : SourceCurrentConjunctionTupleBudget.sample budget
      (SourceCurrentConjunctionTuples.tuples edges) = first :: rest)
    (fits : rest.length + 1 ≤ budget)
    (processed : SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) exposed = .done rows after) :
    run p h budget nodes before = .done (.positive rest.length rows) after := by
  have within : ¬budget < (first :: rest).length := by simpa only [List.length_cons] using Nat.not_lt.mpr fits
  simp only [run, read, Outcome.bind, sampled, within, ↓reduceIte, processed]

/-- Every fitting sample is the full tuple list and executes the exact existing row worker. -/
theorem fits_rows (p h budget : Nat) (nodes : List Node) (before exposed : Physical Symbol Formula)
    (edges : List (List Edge))
    (read : SourceCurrentConjunctionRowsWorker.exposures h nodes before = .done edges exposed)
    (fits : (SourceCurrentConjunctionTupleBudget.sample budget
      (SourceCurrentConjunctionTuples.tuples edges)).length ≤ budget) :
    run p h budget nodes before =
      (SourceCurrentConjunctionRowsWorker.rows p h nodes before).bind fun rows after =>
        .done (match SourceCurrentConjunctionTuples.tuples edges with
          | [] => .zero
          | _ :: rest => .positive rest.length rows) after := by
  have entire := SourceCurrentConjunctionTupleBudget.sample_eq_of_fits budget
    (SourceCurrentConjunctionTuples.tuples edges) fits
  have within : ¬budget < (SourceCurrentConjunctionTuples.tuples edges).length := by
    rw [entire] at fits
    exact Nat.not_lt.mpr fits
  simp only [run, SourceCurrentConjunctionRowsWorker.rows, read, Outcome.bind, entire, within, ↓reduceIte]
  cases selected : SourceCurrentConjunctionTuples.tuples edges with
  | nil => rfl
  | cons first rest => rfl

/-- A completed positive admission supplies its actual charge bound and exact full row execution. -/
theorem positive_rows (p h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (predecessor : Nat) (rows : List (List (List Node)))
    (done : run p h budget nodes before = .done (.positive predecessor rows) after) :
    predecessor + 1 ≤ budget ∧
      SourceCurrentConjunctionRowsWorker.rows p h nodes before = .done rows after := by
  unfold run at done
  cases read : SourceCurrentConjunctionRowsWorker.exposures h nodes before with
  | failed fault exposed => simp only [read, Outcome.bind] at done; cases done
  | done edges exposed =>
      simp only [read, Outcome.bind] at done
      split at done
      · cases done
      · rename_i fits
        have within : (SourceCurrentConjunctionTupleBudget.sample budget
            (SourceCurrentConjunctionTuples.tuples edges)).length ≤ budget := Nat.le_of_not_gt fits
        have entire := SourceCurrentConjunctionTupleBudget.sample_eq_of_fits budget
          (SourceCurrentConjunctionTuples.tuples edges) within
        cases sampled : SourceCurrentConjunctionTupleBudget.sample budget
            (SourceCurrentConjunctionTuples.tuples edges) with
        | nil => simp only [sampled] at done; cases done
        | cons first rest =>
            simp only [sampled] at done
            cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) exposed with
            | failed fault final => simp only [processed] at done; cases done
            | done result final =>
                simp only [processed] at done
                cases done
                constructor
                · simpa only [sampled, List.length_cons] using within
                · have full : SourceCurrentConjunctionTuples.tuples edges = first :: rest := entire.symm.trans sampled
                  simp only [SourceCurrentConjunctionRowsWorker.rows, read, Outcome.bind, full, processed]

/-- Positive admission cannot spend more than the remaining raw tuple budget. -/
theorem positive_charge (p h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (predecessor : Nat) (rows : List (List (List Node)))
    (done : run p h budget nodes before = .done (.positive predecessor rows) after) :
    0 < predecessor + 1 ∧ predecessor + 1 ≤ budget :=
  ⟨Nat.zero_lt_succ _, (positive_rows p h budget nodes before after predecessor rows done).1⟩

end MicroCFTA.SourceCurrentConjunctionTupleAdmission
