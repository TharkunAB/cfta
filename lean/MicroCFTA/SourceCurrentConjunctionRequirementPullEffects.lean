import MicroCFTA.SourceCurrentConjunctionRequirementPull
import MicroCFTA.SourceCurrentConjunctionRowsWarmEffects

/-!
# Physical effects of actual class demand

Only the actual pending jobs need resident operands. The collected prefix
adds no physical work. Empty results and faults retain the exact reached
state. The proof does not execute or require the unused job suffix.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementPullEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRowsWorker (Physical Job Outcome)
open SourceCurrentConjunctionRequirementPull
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- An actual singleton projection preserves full physical readiness on every outcome. -/
theorem projection_effects (p h : Nat) (job : Job Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap job.1) :
    Effects before (projection p h job before).state := by
  have kept : Effects before (SourceCurrentConjunctionRowsWorker.projections p h [job] before).state :=
    Eq.mp (by congr <;> exact Subsingleton.elim _ _)
      (SourceCurrentConjunctionRowsWarmEffects.projections_effects p h [job] before ready
        (by intro next member; cases List.mem_singleton.mp member; exact available))
  cases actual : SourceCurrentConjunctionRowsWorker.projections p h [job] before with
  | failed fault after => simpa only [projection, actual, Outcome.bind, Outcome.state] using kept
  | done values after => simpa only [projection, actual, Outcome.bind, Outcome.state] using kept

/-- The complete finite cursor preserves effects without forcing its unused suffix. -/
theorem run_effects (p h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (available : ∀ job ∈ cursor.pending, Values before.heap job.1) :
    Effects before (run p h cursor before).state := by
  rcases cursor with ⟨jobs, collected⟩
  induction jobs generalizing collected before with
  | nil => simpa only [run_nil, Outcome.state] using Effects.refl before ready
  | cons job rest ih =>
      have first := projection_effects p h job before ready (available job List.mem_cons_self)
      cases actual : projection p h job before with
      | failed fault after =>
          rw [run_failed p h job rest collected before after fault actual]
          simpa only [actual, Outcome.state] using first
      | done value middle =>
          have kept : Effects before middle := by simpa only [actual, Outcome.state] using first
          cases empty : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              rw [run_step]
              simpa only [step, actual, Outcome.bind, empty, ite_true, Outcome.state] using kept
          | false =>
              rw [run_more p h job rest collected before middle value actual empty]
              apply kept.trans
              apply ih (collected := collected ++ [value]) (before := middle) kept.ready
              intro next member node included
              exact kept.keeps.available node
                (available next (List.mem_cons_of_mem _ member) node included)

/-- Original forest residency derives the effect premises of the literal class job order. -/
theorem classConjunction_effects (p h : Nat) (forests : List (List Node))
    (paths : EqualityNormalize.Class) (before : Physical Symbol Formula)
    (ready : Ready before) (available : ∀ forest ∈ forests, Values before.heap forest) :
    Effects before (classConjunction p h forests paths before).state := by
  apply run_effects p h (start forests paths) before ready
  intro job member
  obtain ⟨forest, included, present⟩ := List.mem_flatMap.mp member
  obtain ⟨path, _, same⟩ := List.mem_map.mp present
  cases same
  exact available forest included

end MicroCFTA.SourceCurrentConjunctionRequirementPullEffects
