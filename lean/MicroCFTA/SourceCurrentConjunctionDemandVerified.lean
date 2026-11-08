import MicroCFTA.SourceCurrentConjunctionDemandCompletion
import MicroCFTA.SourceCurrentConjunctionDemandNumeric

/-!
# Initial computed ceilings for complete demand admission

Current input facts derive one actual admission graph.
The original heap scalar and tuple budget determine both worker ceilings.
Every sufficient pair returns the same result and full physical state.
No future execution or tuple-count bound is an input.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandVerified
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsWorker (Physical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects RowsReady)
open SourceCurrentMemoMergeResourceControl (Fits)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Initial resources derive complete demand admission at every computed sufficient pair. -/
theorem complete (budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (fits : Fits resource before.heap) (length : nodes.length ≤ resource)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    ∃ result after,
      (∀ p h,
        SourceCurrentConjunctionProjectionResources.workerFuel
          (SourceCurrentConjunctionTupleBounds.shapeThrough alphabet (max resource budget)) ≤ p →
        SourceCurrentProjectionUnionResources.readFuel
          (SourceCurrentConjunctionWorklistResources.step alphabet (max resource budget)) ≤ h →
        SourceCurrentConjunctionDemandAdmission.run p h budget nodes before = .done result after) ∧
      Fits (SourceCurrentConjunctionWorklistResources.step alphabet (max resource budget)) after.heap ∧
      Effects before after ∧
      (match result with | .positive _ rows => RowsReady after rows | _ => True) := by
  obtain ⟨result, after, ⟨p, h, stable⟩, effects, rows⟩ :=
    SourceCurrentConjunctionDemandCompletion.admission_complete budget nodes before ready available closed
  have actual := stable p h (Nat.le_refl _) (Nat.le_refl _)
  have graph := SourceCurrentConjunctionDemandExecution.admission_graph actual
  have bounded := SourceCurrentConjunctionDemandNumeric.bound graph alphabet resource
    ready available closed fits length known
  exact ⟨result, after, bounded.2, bounded.1, effects, rows⟩

end MicroCFTA.SourceCurrentConjunctionDemandVerified
