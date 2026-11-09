import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
import MicroCFTA.SourceCurrentConjunctionRequirementCellsValues
import MicroCFTA.SourceCurrentConjunctionRowsProbes

/-!
# Clean probes through actual shared requirement forcing

Pending cells execute their actual cursor run. Each demanded singleton
projection retains clean probes at its successful or failed heap. Current
residency and readiness derive every later job premise. Cached hits,
columns, and missing handles retain the original heap. No future successful
force or closed-input premise is supplied.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsProbes
open InternedConstructorTemplates (Value EdgeKey)
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsWorker (Physical Job Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRequirementPull (Cursor projection run)
open SourceCurrentConjunctionRequirementCells (lookup force forceStep force_step update)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem projection_probes (p h : Nat) (job : Job Symbol Formula)
    (before : Physical Symbol Formula) (ready : Ready before) (probes : ProbeHeap before.heap)
    (available : Values before.heap job.1) : ProbeHeap (projection p h job before).state.heap := by
  have clean : ProbeHeap (SourceCurrentConjunctionRowsWorker.projections p h [job] before).state.heap :=
    Eq.mp (by congr <;> exact Subsingleton.elim _ _)
      (SourceCurrentConjunctionRowsProbes.projections_heap p h [job] before ready probes
        (by intro next member; cases List.mem_singleton.mp member; exact available))
  cases actual : SourceCurrentConjunctionRowsWorker.projections p h [job] before with
  | failed fault after => simpa only [projection, actual, Outcome.bind, Outcome.state] using clean
  | done values after => simpa only [projection, actual, Outcome.bind, Outcome.state] using clean

private theorem run_probes (p h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : ProbeHeap before.heap)
    (available : ∀ job ∈ cursor.pending, Values before.heap job.1) :
    ProbeHeap (run p h cursor before).state.heap := by
  rcases cursor with ⟨jobs, collected⟩
  induction jobs generalizing collected before with
  | nil => simpa only [SourceCurrentConjunctionRequirementPull.run_nil, Outcome.state] using probes
  | cons job rest ih =>
      have clean := projection_probes p h job before ready probes (available job List.mem_cons_self)
      have first := SourceCurrentConjunctionRequirementPullEffects.projection_effects
        p h job before ready (available job List.mem_cons_self)
      cases actual : projection p h job before with
      | failed fault after =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job rest collected before after fault actual]
          simpa only [actual, Outcome.state] using clean
      | done value middle =>
          have kept : Effects before middle := by simpa only [actual, Outcome.state] using first
          have current : ProbeHeap middle.heap := by simpa only [actual, Outcome.state] using clean
          cases empty : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              rw [SourceCurrentConjunctionRequirementPull.run_step]
              simpa only [SourceCurrentConjunctionRequirementPull.step, actual, Outcome.bind,
                empty, ite_true, Outcome.state] using current
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.run_more p h job rest collected before middle value actual empty]
              apply ih (collected := collected ++ [value]) (before := middle) kept.ready current
              intro next member node included
              exact kept.keeps.available node
                (available next (List.mem_cons_of_mem _ member) node included)

/-- Actual finite forcing retains clean probes at every returned heap, including projection faults. -/
theorem force_probes (p h handle : Nat) (before : Cells) (ready : Ready before.physical)
    (probes : ProbeHeap before.physical.heap)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before) :
    ProbeHeap (force p h handle before).state.physical.heap := by
  cases found : lookup handle before with
  | none =>
      rw [force_step]
      simpa only [forceStep, found, SourceCurrentConjunctionRequirementCells.Outcome.state] using probes
  | some cell =>
      cases cell with
      | done nodes =>
          rw [SourceCurrentConjunctionRequirementCells.force_hit p h handle nodes before found]
          exact probes
      | column nodes =>
          rw [force_step]
          simpa only [forceStep, found, update, SourceCurrentConjunctionRequirementCells.Outcome.state] using probes
      | pending cursor =>
          have clean := run_probes p h cursor before.physical ready probes (values handle (.pending cursor) found).2
          cases actual : force p h handle before with
          | done nodes after =>
              have same := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
              rw [same] at clean
              exact clean
          | failed diagnostic after =>
              obtain ⟨stopped, fault, _, same, _⟩ :=
                SourceCurrentConjunctionRequirementCellsExecution.force_pending_failed found actual
              rw [same] at clean
              exact clean

end MicroCFTA.SourceCurrentConjunctionRequirementCellsProbes
