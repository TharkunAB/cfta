import MicroCFTA.SourceCurrentConjunctionTuplePullTotalCompletion
import MicroCFTA.SourceCurrentConjunctionTuplePullClosedSample
import MicroCFTA.SourceCurrentConjunctionTuplePullReplay
import MicroCFTA.SourceCurrentConjunctionTuplePullResources
import MicroCFTA.SourceCurrentConjunctionFirstDemandReplay

/-!
# Computed initial read allowance for physical tuple sampling

The original operand count and initial heap resource determine the read
allowance. Initial readiness supplies one completed observation. Actual
first-demand receipts replay that observation at the computed allowance.
No completed future trace or sufficient read allowance is an input.
This is a mathematical heap bound. Native widths and scan cost remain
separate obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullNumeric
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsWorker (Physical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTuplePull (start)
open SourceCurrentConjunctionTuplePullTotal (Result sample)
open SourceCurrentConjunctionTuplePullDriveEffects (StatusInputs)
open SourceCurrentConjunctionTuplePullClosedSample (ResultClosed)
open SourceCurrentConjunctionTuplePullReadTrace (demands)
open SourceCurrentConjunctionExposureResources (forecast)
open SourceCurrentMemoMergeResourceControl (Fits)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

/-- Original support size and initial heap resource supply the common read allowance. -/
def fuel (count resource : Nat) : Nat :=
  SourceCurrentProjectionUnionResources.readFuel (forecast count resource)

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Initial resources derive the actual complete sample at every sufficient computed allowance. -/
theorem sample_complete (budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (resource : Nat) (ready : Ready before) (available : Values before.heap nodes)
    (closed : ClosedValues nodes) (fits : Fits resource before.heap) :
    ∃ result after,
      (∀ h, fuel nodes.length resource ≤ h → sample h budget nodes before = .done result after) ∧
      Effects before after ∧ StatusInputs after.heap result.toStatus ∧
      SourceCurrentConjunctionTuplePullAdmission.Bounded budget result.toStatus ∧
      ResultClosed result ∧ Fits (forecast nodes.length resource) after.heap := by
  letI : DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula)) :=
    fun left right => Classical.propDecidable (left = right)
  obtain ⟨oldH, result, after, stable, effects, supported, bounded⟩ :=
    SourceCurrentConjunctionTuplePullTotalCompletion.sample_complete budget nodes before ready available closed
  have actual := stable oldH (Nat.le_refl _)
  obtain ⟨steps, eventual⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation oldH budget nodes before
  have observed := eventual 0
  simp only [Nat.add_zero, actual, SourceCurrentConjunctionTuplePullTotal.observe] at observed
  obtain ⟨rows, reads⟩ := SourceCurrentConjunctionTuplePullReadTrace.drive_reads
    steps oldH budget (start nodes) [] before after result.toStatus observed
  have included := SourceCurrentConjunctionTuplePullReadTrace.demands_supported
    steps oldH budget (start nodes) [] before nodes
    (SourceCurrentConjunctionTuplePullReads.start_supported nodes)
  have replay := SourceCurrentConjunctionFirstDemandReplay.original_replay reads nodes included resource
    ready.semantic ready.costs available closed fits before.equality (fuel nodes.length resource) (Nat.le_refl _)
  have replayed := SourceCurrentConjunctionTuplePullReplay.drive_replay
    steps oldH (fuel nodes.length resource) budget (start nodes) [] before after result.toStatus rows observed replay
  have done : sample (fuel nodes.length resource) budget nodes before = .done result after :=
    SourceCurrentConjunctionTuplePullTotal.run_of_observation steps (fuel nodes.length resource) budget
      (start nodes) [] before (.done result after) replayed
  have returned := SourceCurrentConjunctionTuplePullResources.sample_fits (fuel nodes.length resource)
    budget nodes before after result done resource ready available closed fits
  have closedResult := SourceCurrentConjunctionTuplePullClosedSample.sample_closed
    (fuel nodes.length resource) budget nodes before ready available closed
  refine ⟨result, after, ?_, effects, supported, bounded, closedResult.2 result after done, returned⟩
  intro h enough
  exact SourceCurrentConjunctionTuplePullStability.sample_done_stable done enough

end MicroCFTA.SourceCurrentConjunctionTuplePullNumeric
