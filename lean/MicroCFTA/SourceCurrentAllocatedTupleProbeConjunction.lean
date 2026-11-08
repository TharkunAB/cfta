import MicroCFTA.SourceCurrentAllocatedProbeConjunction
import MicroCFTA.SourceCurrentConjunctionDemandWorklistExecution
import MicroCFTA.SourceCurrentConjunctionDemandWorklistEffects

/-!
# Filtered probes through actual tuple-budget calls

The completed call graph replays the same worker at its derived bounds.
Probe preservation follows that actual execution. The legacy probe laws
remain available to the legacy row worker.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeConjunction
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentConjunctionRowsAllocation (Ready)
open InternedFreshOrdinaryProbeHeap (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula

/-- The actual completed tuple call retains probes in its returned heap. -/
theorem tuple_call_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {memo saved : SourceCurrentEmptinessMemo.Memo}
    {query : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionDemandWorklistExecution.Call budget memo query before answer after saved)
    (ready : Ready before) (available : Available before.heap query) (probes : Heap before.heap) :
    Heap after.heap := by
  obtain ⟨p, h, done⟩ := SourceCurrentConjunctionDemandWorklistExecution.call_complete actual
  have kept : Heap (SourceCurrentConjunctionDemandWorker.call p h budget memo query before).state.heap :=
    Eq.mp (by congr <;> exact Subsingleton.elim _ _)
      (SourceCurrentConjunctionDemandWorklistEffects.call_probes p h budget memo query before ready probes available)
  have completed := done p h (Nat.le_refl _) (Nat.le_refl _)
  simpa only [completed, SourceCurrentConjunctionWorker.Outcome.state] using kept

end MicroCFTA.SourceCurrentAllocatedProbeConjunction
