import MicroCFTA.SourceCurrentConjunctionTupleAdmission
import MicroCFTA.SourceCurrentConjunctionRowsWarmEffects
import MicroCFTA.SourceCurrentConjunctionRowsWorkerEffects
import MicroCFTA.SourceCurrentConjunctionRowsProbes
import MicroCFTA.SourceCurrentConjunctionRowsWorkerActual

set_option autoImplicit false
open scoped Classical

/-!
# Actual physical effects of tuple-budget admission

Every outcome retains readiness and old records. This includes exposure
failure, overflow, zero charge, and tuple failure. Completed positive rows
retain the existing row worker's closed available operands. These laws use
the existing eager exposure schedule. They do not specify native lazy demand.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleAdmissionEffects
open InternedConstructorTemplates
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTupleAdmission (run Result)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap

private theorem resident_tuples (edges : List (List (EdgeValue Symbol Guard)))
    (state : Physical Symbol Formula) (resident : ∀ row ∈ edges, Edges state.heap row) :
    ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges, Edges state.heap tuple := by
  intro tuple member edge included
  obtain ⟨row, present, own⟩ := List.mem_flatten.mp
    (SourceCurrentConjunctionTuples.tuples_members edges tuple member edge included)
  exact resident row present edge own

/-- All actual admission outcomes preserve full readiness, old records, and equality allocations. -/
theorem run_effects (p h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap nodes) :
    Effects before (run p h budget nodes before).state := by
  have first := SourceCurrentConjunctionRowsExposureFields.exposures_effects h nodes before ready available
  cases read : SourceCurrentConjunctionRowsWorker.exposures h nodes before with
  | failed fault exposed =>
      simpa only [SourceCurrentConjunctionTupleAdmission.run, read, Outcome.bind, Outcome.state] using first.1
  | done edges exposed =>
      have kept : Effects before exposed := by simpa only [read, Outcome.state] using first.1
      have loaded := first.2
      rw [read] at loaded
      have resident := resident_tuples edges exposed (fun row member => (loaded row member).1)
      simp only [SourceCurrentConjunctionTupleAdmission.run, read, Outcome.bind]
      by_cases overflow : budget < (SourceCurrentConjunctionTupleBudget.sample budget
          (SourceCurrentConjunctionTuples.tuples edges)).length
      · simpa only [overflow, ↓reduceIte, Outcome.state] using kept
      · simp only [overflow, ↓reduceIte]
        have entire := SourceCurrentConjunctionTupleBudget.sample_eq_of_fits budget
          (SourceCurrentConjunctionTuples.tuples edges) (Nat.le_of_not_gt overflow)
        cases sampled : SourceCurrentConjunctionTupleBudget.sample budget
            (SourceCurrentConjunctionTuples.tuples edges) with
        | nil => simpa only [sampled, Outcome.state] using kept
        | cons head tail =>
            have full : SourceCurrentConjunctionTuples.tuples edges = head :: tail := entire.symm.trans sampled
            have later := SourceCurrentConjunctionRowsWarmEffects.tuples_effects p h (head :: tail)
              exposed kept.ready (by simpa only [← full] using resident)
            dsimp only
            cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (head :: tail) exposed <;>
              simpa only [processed, Outcome.state] using kept.trans later

/-- Every actual admission outcome retains clean stored recursive probes. -/
theorem run_probes (p h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : ProbeHeap before.heap) (available : Values before.heap nodes) :
    ProbeHeap (run p h budget nodes before).state.heap := by
  have clean := SourceCurrentConjunctionExposureProbes.exposures_heap h nodes before
    ready.semantic ready.costs probes available
  have first := SourceCurrentConjunctionRowsExposureFields.exposures_effects h nodes before ready available
  cases read : SourceCurrentConjunctionRowsWorker.exposures h nodes before with
  | failed fault exposed =>
      simpa only [SourceCurrentConjunctionTupleAdmission.run, read, Outcome.bind, Outcome.state] using clean
  | done edges exposed =>
      have kept : Effects before exposed := by simpa only [read, Outcome.state] using first.1
      have exposedClean : ProbeHeap exposed.heap := by simpa only [read, Outcome.state] using clean
      have loaded := first.2
      rw [read] at loaded
      have resident := resident_tuples edges exposed (fun row member => (loaded row member).1)
      simp only [SourceCurrentConjunctionTupleAdmission.run, read, Outcome.bind]
      by_cases overflow : budget < (SourceCurrentConjunctionTupleBudget.sample budget
          (SourceCurrentConjunctionTuples.tuples edges)).length
      · simpa only [overflow, ↓reduceIte, Outcome.state] using exposedClean
      · simp only [overflow, ↓reduceIte]
        have entire := SourceCurrentConjunctionTupleBudget.sample_eq_of_fits budget
          (SourceCurrentConjunctionTuples.tuples edges) (Nat.le_of_not_gt overflow)
        cases sampled : SourceCurrentConjunctionTupleBudget.sample budget
            (SourceCurrentConjunctionTuples.tuples edges) with
        | nil => simpa only [sampled, Outcome.state] using exposedClean
        | cons head tail =>
            have full : SourceCurrentConjunctionTuples.tuples edges = head :: tail := entire.symm.trans sampled
            have later := SourceCurrentConjunctionRowsProbes.tuples_heap p h (head :: tail) exposed
              kept.ready exposedClean (by simpa only [← full] using resident)
            dsimp only
            cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (head :: tail) exposed <;>
              simpa only [processed, Outcome.state] using later

/-- Overflow retains the exact equality cache from before the operand reads. -/
theorem overflow_equality (p h budget : Nat) (nodes : List Node)
    (before exposed : Physical Symbol Formula) (edges : List (List (EdgeValue Symbol Guard)))
    (read : SourceCurrentConjunctionRowsWorker.exposures h nodes before = .done edges exposed)
    (overflow : budget < (SourceCurrentConjunctionTupleBudget.sample budget
      (SourceCurrentConjunctionTuples.tuples edges)).length) :
    run p h budget nodes before = .done .overflow exposed ∧ exposed.equality = before.equality :=
  ⟨SourceCurrentConjunctionTupleAdmission.run_overflow p h budget nodes before exposed edges read overflow,
    (SourceCurrentConjunctionRowsWorkerActual.exposures_graph read).2⟩

/-- Zero charge retains the exact equality cache from before the operand reads. -/
theorem zero_equality (p h budget : Nat) (nodes : List Node)
    (before exposed : Physical Symbol Formula) (edges : List (List (EdgeValue Symbol Guard)))
    (read : SourceCurrentConjunctionRowsWorker.exposures h nodes before = .done edges exposed)
    (zero : SourceCurrentConjunctionTupleBudget.sample budget
      (SourceCurrentConjunctionTuples.tuples edges) = []) :
    run p h budget nodes before = .done .zero exposed ∧ exposed.equality = before.equality :=
  ⟨SourceCurrentConjunctionTupleAdmission.run_zero p h budget nodes before exposed edges read zero,
    (SourceCurrentConjunctionRowsWorkerActual.exposures_graph read).2⟩

/-- Positive admitted rows retain closed available operands at their actual returned heap. -/
theorem positive_closed {Formula : Type} (p h budget : Nat)
    (nodes : List (Value SourcePruningTemplates.Symbol (SourceSymbolicIndex.Constraint Formula)))
    (before after : Physical SourcePruningTemplates.Symbol Formula)
    (predecessor : Nat)
    (rows : List (List (List (Value SourcePruningTemplates.Symbol (SourceSymbolicIndex.Constraint Formula)))))
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (done : run p h budget nodes before = .done (.positive predecessor rows) after) :
    ∀ row ∈ rows, ∀ operands ∈ row, Values after.heap operands ∧ ClosedValues operands := by
  have exactRows := (SourceCurrentConjunctionTupleAdmission.positive_rows p h budget nodes before after
    predecessor rows done).2
  have preserved := SourceCurrentConjunctionRowsWorkerEffects.rows_effects p h nodes before
    ready.semantic.ready.semantic ready.semantic.ready.covered available closed
  simpa only [exactRows] using preserved.2.2.2.2

end MicroCFTA.SourceCurrentConjunctionTupleAdmissionEffects
