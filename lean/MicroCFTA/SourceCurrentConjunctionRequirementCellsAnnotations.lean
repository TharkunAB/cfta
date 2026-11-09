import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
import MicroCFTA.SourceCurrentConjunctionRequirementCellsClosed
import MicroCFTA.SourceCurrentConjunctionRowsAnnotationOutcome

/-!
# Heap annotations through actual shared-cell forcing

Every demanded singleton projection preserves the original annotation
predicate at its exact returned heap. Current cell values and closedness
derive the captured job inputs. Failed pending forces retain the same
physical endpoint as their failed cursor run. Cached cells, columns, and
missing handles leave the native heap unchanged. No future successful
projection or annotation certificate is supplied.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsAnnotations
open InternedConstructorTemplates (EdgeKey)
open SourceEqualityAnnotationHeap (Heap)
open SourceCurrentConjunctionRowsWorker (Physical Job Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionCompletionReads (Inputs)
open SourceCurrentConjunctionRequirementPull (Cursor projection run)
open SourceCurrentConjunctionRequirementCells (lookup force forceStep force_step update)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem projection_heap (annotation : Guard → Prop) (p h : Nat) (job : Job Symbol Formula)
    (before : Physical Symbol Formula) (ready : Ready before)
    (inputs : Inputs before.heap [job]) (heap : Heap annotation before.heap) :
    Heap annotation (projection p h job before).state.heap := by
  have preserved : Heap annotation
      (SourceCurrentConjunctionRowsWorker.projections p h [job] before).state.heap :=
    SourceCurrentConjunctionRowsAnnotationOutcome.projections_heap annotation p h [job] before
      ready.semantic ready.costs inputs heap
  cases actual : SourceCurrentConjunctionRowsWorker.projections p h [job] before with
  | failed fault after => simpa only [projection, actual, Outcome.bind, Outcome.state] using preserved
  | done values after => simpa only [projection, actual, Outcome.bind, Outcome.state] using preserved

private theorem run_heap (annotation : Guard → Prop) (p h : Nat) (cursor : Cursor Symbol Formula)
    (before : Physical Symbol Formula) (ready : Ready before)
    (inputs : Inputs before.heap cursor.pending) (heap : Heap annotation before.heap) :
    Heap annotation (run p h cursor before).state.heap := by
  rcases cursor with ⟨jobs, collected⟩
  change Inputs before.heap jobs at inputs
  induction jobs generalizing collected before with
  | nil => simpa only [SourceCurrentConjunctionRequirementPull.run_nil, Outcome.state] using heap
  | cons job rest ih =>
      have own := inputs job List.mem_cons_self
      have preserved := projection_heap annotation p h job before ready
        (by intro next member; cases List.mem_singleton.mp member; exact own) heap
      have first := SourceCurrentConjunctionRequirementPullEffects.projection_effects p h job before ready own.1
      cases actual : projection p h job before with
      | failed fault after =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job rest collected before after fault actual]
          simpa only [actual, Outcome.state] using preserved
      | done value middle =>
          have kept : Effects before middle := by simpa only [actual, Outcome.state] using first
          have current : Heap annotation middle.heap := by simpa only [actual, Outcome.state] using preserved
          cases tested : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              rw [SourceCurrentConjunctionRequirementPull.run_step]
              simpa only [SourceCurrentConjunctionRequirementPull.step, actual, Outcome.bind,
                tested, ite_true, Outcome.state] using current
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.run_more p h job rest collected before middle value actual tested]
              exact ih (collected := collected ++ [value]) (before := middle) (ready := kept.ready)
                (inputs := SourceCurrentConjunctionCompletionReads.Inputs.keeps
                  (fun next member => inputs next (List.mem_cons_of_mem _ member)) kept.keeps) (heap := current)

/-- All actual force outcomes preserve the original heap annotation predicate. -/
theorem force_heap (annotation : Guard → Prop) (p h handle : Nat) (before : Cells)
    (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before)
    (heap : Heap annotation before.physical.heap) :
    Heap annotation (force p h handle before).state.physical.heap := by
  cases found : lookup handle before with
  | none =>
      rw [force_step]
      simpa only [forceStep, found, SourceCurrentConjunctionRequirementCells.Outcome.state] using heap
  | some cell =>
      cases cell with
      | done nodes =>
          rw [SourceCurrentConjunctionRequirementCells.force_hit p h handle nodes before found]
          exact heap
      | column nodes =>
          rw [force_step]
          simpa only [forceStep, found, update, SourceCurrentConjunctionRequirementCells.Outcome.state] using heap
      | pending cursor =>
          have inputs : Inputs before.physical.heap cursor.pending := by
            intro job member
            exact ⟨(values handle (.pending cursor) found).2 job member,
              (closed handle (.pending cursor) found).2 job member⟩
          have preserved := run_heap annotation p h cursor before.physical ready inputs heap
          cases actual : force p h handle before with
          | done nodes after =>
              have same := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
              rw [same] at preserved
              exact preserved
          | failed diagnostic after =>
              obtain ⟨stopped, fault, _, same, _⟩ :=
                SourceCurrentConjunctionRequirementCellsExecution.force_pending_failed found actual
              rw [same] at preserved
              exact preserved

end MicroCFTA.SourceCurrentConjunctionRequirementCellsAnnotations
