import MicroCFTA.SourceCurrentConjunctionTupleWorklistResources

/-!
# Uniform numeric replay of actual tuple admission

The initial operand width and heap scalar fix both worker ceilings.
Overflow and zero charge replay only their actual operand exposures.
Positive charge replays the full tuple list in its actual source order.
The existing finite guard forecasts retain their noncomputable boundary.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleAdmissionNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionTupleExecution (Admission)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "step" => SourceCurrentConjunctionWorklistResources.step
local notation "projectionFuel" => SourceCurrentConjunctionProjectionResources.workerFuel
local notation "readFuel" => SourceCurrentProjectionUnionResources.readFuel

/-- The full row envelope includes the earlier exposure-only envelope. -/
theorem exposure_le_step (alphabet : List Guard) (resource : Nat) :
    SourceCurrentConjunctionExposureResources.forecast resource (resource + 1) ≤ step alphabet resource :=
  SourceCurrentConjunctionRowsResources.tupleSchedule_ge alphabet resource _ _ _

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- One original scalar bounds actual admission and replays it at every larger pair of ceilings. -/
theorem bound {budget : Nat} {nodes : List (Value Symbol Guard)} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) (alphabet : List Guard) (resource : Nat)
    (ready : Ready before) (available : Values before.heap nodes) (noFree : ClosedValues nodes)
    (fits : Fits resource before.heap) (length : nodes.length ≤ resource)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (step alphabet resource) after.heap ∧
      ∀ p h, projectionFuel (SourceCurrentConjunctionTupleBounds.shapeThrough alphabet resource) ≤ p →
        readFuel (step alphabet resource) ≤ h →
        SourceCurrentConjunctionTupleAdmission.run p h budget nodes before = .done result after := by
  cases actual with
  | overflow reads tooMany =>
      have exposed := SourceCurrentConjunctionExposureResources.bounded reads resource (resource + 1)
        ready.semantic ready.costs available noFree (fits.mono (Nat.le_succ _)) length
      have width := exposure_le_step alphabet resource
      refine ⟨exposed.1.mono width, ?_⟩
      intro p h _ enoughH
      exact SourceCurrentConjunctionTupleAdmission.run_overflow p h _ _ _ _ _
        (exposed.2.2.2 before.equality h
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono width) enoughH)) tooMany
  | zero reads noTuples =>
      have exposed := SourceCurrentConjunctionExposureResources.bounded reads resource (resource + 1)
        ready.semantic ready.costs available noFree (fits.mono (Nat.le_succ _)) length
      have width := exposure_le_step alphabet resource
      refine ⟨exposed.1.mono width, ?_⟩
      intro p h _ enoughH
      apply SourceCurrentConjunctionTupleAdmission.run_zero p h _ _ _ _ _
        (exposed.2.2.2 before.equality h
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono width) enoughH))
      simp only [noTuples, SourceCurrentConjunctionTupleBudget.sample, List.take_nil]
  | @positive predecessor nodes before after edges heap requirements reads count spent tuples =>
      have numeric := SourceCurrentConjunctionRowsResources.bound (.run reads tuples) alphabet resource (resource + 1)
        ready available noFree (fits.mono (Nat.le_succ _)) length known
      have exposed := SourceCurrentConjunctionExposureResources.bounded reads resource (resource + 1)
        ready.semantic ready.costs available noFree (fits.mono (Nat.le_succ _)) length
      refine ⟨numeric.1, ?_⟩
      intro p h enoughP enoughH
      have readDone := exposed.2.2.2 before.equality h
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono (exposure_le_step alphabet resource)) enoughH)
      have rowsDone := numeric.2.2 p h enoughP enoughH
      have within : (SourceCurrentConjunctionTupleBudget.sample budget
          (SourceCurrentConjunctionTuples.tuples edges)).length ≤ budget := by
        have full : (SourceCurrentConjunctionTuples.tuples edges).length ≤ budget := by omega
        simp only [SourceCurrentConjunctionTupleBudget.sample, List.length_take]
        omega
      rw [SourceCurrentConjunctionTupleAdmission.fits_rows p h budget nodes before
        ⟨heap, before.equality⟩ edges readDone within]
      simp only [rowsDone, SourceCurrentConjunctionRowsWorker.Outcome.bind]
      cases selected : SourceCurrentConjunctionTuples.tuples edges with
      | nil => simp only [selected, List.length_nil] at count; omega
      | cons first rest =>
          have predecessorEq : rest.length = predecessor := by
            simp only [selected, List.length_cons] at count
            omega
          simp only [predecessorEq]

end MicroCFTA.SourceCurrentConjunctionTupleAdmissionNumeric
