import MicroCFTA.SourceCurrentConjunctionDemandExecution
import MicroCFTA.SourceCurrentConjunctionTuplePullTotalCompletion
import MicroCFTA.SourceCurrentConjunctionTuplePullClosedSample
import MicroCFTA.SourceCurrentConjunctionTuplePullReadTrace

/-!
# Initial completion of demand admission

Ready closed operands derive a complete actual sample. A fitting positive
sample derives its resident closed tuple rows and their finite allocation.
The returned stable execution needs no supplied successful observation or
future resource bound. Its graph also retains the actual demanded reads.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandCompletion
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsWorker (Physical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects RowsReady)
open SourceCurrentConjunctionRowsWorkerCompletion (StableRun)
open SourceCurrentConjunctionDemandExecution (Admission)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Initial readiness derives stable demand admission and all returned requirement invariants. -/
theorem admission_complete (budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    ∃ result after,
      StableRun (fun p h => SourceCurrentConjunctionDemandAdmission.run p h budget nodes before) result after ∧
      Effects before after ∧
      (match result with | .positive _ rows => RowsReady after rows | _ => True) := by
  obtain ⟨h, selected, middle, stable, kept, resident, _bounded⟩ :=
    SourceCurrentConjunctionTuplePullTotalCompletion.sample_complete budget nodes before ready available closed
  have sampled := stable h (Nat.le_refl _)
  cases selected with
  | overflow tuples cursor =>
      have graph : Admission budget nodes before .overflow middle := .overflow sampled
      exact ⟨.overflow, middle, SourceCurrentConjunctionDemandExecution.admission_complete graph, kept, trivial⟩
  | fit tuples =>
      cases tuples with
      | nil =>
          have graph : Admission budget nodes before .zero middle := .zero sampled
          exact ⟨.zero, middle, SourceCurrentConjunctionDemandExecution.admission_complete graph, kept, trivial⟩
      | cons first rest =>
          have noFree := SourceCurrentConjunctionTuplePullClosedSample.sample_fit h budget nodes before middle
            (first :: rest) sampled ready available closed
          have shapes := SourceCurrentConjunctionTuplePullShapes.sample_fit h budget nodes before middle
            (first :: rest) sampled
          obtain ⟨rows, after, allocated, later, returned⟩ :=
            SourceCurrentConjunctionRowsAllocation.tuples_complete (first :: rest) middle kept.ready resident noFree
              (fun tuple member => SourceCurrentConjunctionRowsAllocation.matching_arity tuple
                (shapes tuple member).2.1)
          have graph : Admission budget nodes before (.positive rest.length rows) after := .positive sampled allocated
          exact ⟨.positive rest.length rows, after,
            SourceCurrentConjunctionDemandExecution.admission_complete graph, kept.trans later, returned⟩

end MicroCFTA.SourceCurrentConjunctionDemandCompletion

namespace MicroCFTA.SourceCurrentConjunctionDemandExecution
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Tuples)
open SourceCurrentConjunctionCompletionReads (Exposures)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem sample_reads {h budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTuplePullTotal.Result Symbol Formula}
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after) :
    ∃ reads rows, Exposures reads before.heap rows after.heap ∧
      (∀ node ∈ reads, node ∈ nodes) ∧ after.equality = before.equality := by
  obtain ⟨reads, rows, exposed, included⟩ :=
    SourceCurrentConjunctionTuplePullReadTrace.sample_reads h budget nodes before after result actual
  have unchanged := SourceCurrentConjunctionTuplePullTotal.run_equality h budget
    (SourceCurrentConjunctionTuplePull.start nodes) [] before
  change (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.equality = before.equality
    at unchanged
  exact ⟨reads, rows, exposed, included, by simpa only [actual, Outcome.state] using unchanged⟩

/-- Every admission retains its actual demand receipt, original support, and sampled allocation. -/
theorem Admission.demand_reads {budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) :
    ∃ h sampled middle reads rows,
      SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done sampled middle ∧
      Exposures reads before.heap rows middle.heap ∧
      (∀ node ∈ reads, node ∈ nodes) ∧ middle.equality = before.equality ∧
      (match result, sampled with
        | .overflow, .overflow _ _ => middle = after
        | .zero, .fit [] => middle = after
        | .positive predecessor requirements, .fit tuples =>
            tuples.length = predecessor + 1 ∧ Tuples tuples middle requirements after
        | _, _ => False) := by
  cases actual with
  | overflow sampled =>
      obtain ⟨reads, rows, exposed, included, equality⟩ := sample_reads sampled
      exact ⟨_, _, _, reads, rows, sampled, exposed, included, equality, rfl⟩
  | zero sampled =>
      obtain ⟨reads, rows, exposed, included, equality⟩ := sample_reads sampled
      exact ⟨_, _, _, reads, rows, sampled, exposed, included, equality, rfl⟩
  | positive sampled allocated =>
      obtain ⟨reads, rows, exposed, included, equality⟩ := sample_reads sampled
      exact ⟨_, _, _, reads, rows, sampled, exposed, included, equality, rfl, allocated⟩

end MicroCFTA.SourceCurrentConjunctionDemandExecution
