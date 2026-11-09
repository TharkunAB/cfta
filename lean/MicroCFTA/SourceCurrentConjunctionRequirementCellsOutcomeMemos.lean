import MicroCFTA.SourceCurrentConjunctionRequirementPullOutcomeMemos
import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
import MicroCFTA.SourceCurrentConjunctionRequirementCellsValues

/-!
# Exact memo bundles through all shared-cell outcomes

A failed pending force retains its final stopped cursor and the ordered
memo calls of the complete failed cursor run. Earlier completed calls and
the terminal projection pass the same returned global bundle. Completed
cells, columns, and missing handles add no global read. The current cell
values derive every pending forest's residency. Closedness is not needed.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsOutcomeMemos
open Cache InternedConstructorTemplates
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementCells
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "canonical" => SourceCurrentConjunctionRequirements.canonical
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Complete forcing retains its actual outcome and every ordered cursor call. -/
inductive ForceReads (p h handle : Nat) : Cells → Outcome Symbol FullSyntax.Formula (List Node) →
    Memos → Memos → Prop where
  | missing (absent : lookup handle before = none) :
      ForceReads p h handle before (.failed (.missing handle) before) memos memos
  | hit (found : lookup handle before = some (.done nodes)) :
      ForceReads p h handle before (.done nodes before) memos memos
  | column (found : lookup handle before = some (.column nodes)) :
      ForceReads p h handle before
        (.done (canonical nodes) (update handle (.done (canonical nodes)) before)) memos memos
  | pending_done (found : lookup handle before = some (.pending cursor))
      (actual : force p h handle before = .done nodes after)
      (calls : SourceCurrentConjunctionRequirementPullOutcomeMemos.RunReads p h cursor before.physical
        (.done nodes after.physical) memos saved) :
      ForceReads p h handle before (.done nodes after) memos saved
  | pending_failed (found : lookup handle before = some (.pending cursor))
      (actual : force p h handle before = .failed diagnostic after)
      (named : diagnostic = .projection handle stopped fault)
      (cached : lookup handle after = some (.pending stopped))
      (calls : SourceCurrentConjunctionRequirementPullOutcomeMemos.RunReads p h cursor before.physical
        (.failed fault after.physical) memos saved) :
      ForceReads p h handle before (.failed diagnostic after) memos saved

/-- Every literal force derives its returned memo bundle, including terminal projection faults. -/
theorem force_memos (p h handle : Nat) (before : Cells) (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (memos : Memos) (valid : Valid before.physical.heap memos) :
    ∃ saved, ForceReads p h handle before (force p h handle before) memos saved ∧
      Valid (force p h handle before).state.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases found : lookup handle before with
  | none =>
      rw [force_step, forceStep_missing p h handle before found]
      exact ⟨memos, .missing found, valid, extends_refl _, rfl⟩
  | some cell =>
      cases cell with
      | done nodes =>
          rw [force_hit p h handle nodes before found]
          exact ⟨memos, .hit found, valid, extends_refl _, rfl⟩
      | column nodes =>
          have completed : force p h handle before =
              .done (canonical nodes) (update handle (.done (canonical nodes)) before) := by
            rw [force_step]
            simp only [forceStep, found]
          rw [completed]
          exact ⟨memos, .column found, valid, extends_refl _, rfl⟩
      | pending cursor =>
          obtain ⟨saved, calls, coherent, retained, same⟩ :=
            SourceCurrentConjunctionRequirementPullOutcomeMemos.run_memos p h cursor before.physical ready
              (values handle (.pending cursor) found).2 memos valid
          cases actual : force p h handle before with
          | done nodes after =>
              have completed := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
              have exactCalls : SourceCurrentConjunctionRequirementPullOutcomeMemos.RunReads p h cursor before.physical
                  (.done nodes after.physical) memos saved := by
                simpa only [completed] using calls
              have finalValid : Valid after.physical.heap saved := by
                simpa only [completed, SourceCurrentConjunctionRowsWorker.Outcome.state] using coherent
              exact ⟨saved, .pending_done found actual exactCalls, finalValid, retained, same⟩
          | failed diagnostic after =>
              obtain ⟨stopped, fault, named, completed, cached⟩ :=
                SourceCurrentConjunctionRequirementCellsExecution.force_pending_failed found actual
              have exactCalls : SourceCurrentConjunctionRequirementPullOutcomeMemos.RunReads p h cursor before.physical
                  (.failed fault after.physical) memos saved := by
                simpa only [completed] using calls
              have finalValid : Valid after.physical.heap saved := by
                simpa only [completed, SourceCurrentConjunctionRowsWorker.Outcome.state] using coherent
              exact ⟨saved, .pending_failed found actual named cached exactCalls, finalValid, retained, same⟩

end MicroCFTA.SourceCurrentConjunctionRequirementCellsOutcomeMemos
