import MicroCFTA.SourceCurrentConjunctionExposureResources
import MicroCFTA.SourceCurrentConjunctionTupleNumeric
import MicroCFTA.SourceCurrentConjunctionGuardUniverse

/-!
# Initial resources for one complete conjunction row construction

The original operand count fixes exposure and tuple counts. Every tuple
uses its preceding actual heap. Kept rows retain both requirement widths.
The fixed initial guard carrier supplies the equality-shape bound.
-/
namespace MicroCFTA.SourceCurrentConjunctionRowsResources
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready Effects Tuple Tuples Rows RowsReady)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
open SourceCurrentConjunctionProjectionResources (workerFuel)
open HeightOrderControlled (iterate)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula

/-- The literal tuple count fixes the sequence of complete tuple envelopes. -/
noncomputable def tupleSchedule (alphabet : List Guard) (count width tuples resource : Nat) : Nat :=
  iterate (SourceCurrentConjunctionTupleNumeric.forecast alphabet count width) tuples resource

/-- The tuple schedule retains its original scalar. -/
theorem tupleSchedule_ge (alphabet : List Guard) (count width tuples resource : Nat) :
    resource ≤ tupleSchedule alphabet count width tuples resource :=
  SourceCurrentMemoMergeNumericControl.iterate_ge _
    (SourceCurrentConjunctionTupleNumeric.forecast_ge alphabet count width) tuples resource

/-- Larger initial scalars retain the same literal tuple schedule. -/
theorem tupleSchedule_mono (alphabet : List Guard) (count width tuples : Nat)
    {first last : Nat} (increase : first ≤ last) :
    tupleSchedule alphabet count width tuples first ≤ tupleSchedule alphabet count width tuples last :=
  SourceCurrentMemoMergeNumericControl.iterate_mono _
    (SourceCurrentConjunctionTupleNumeric.forecast_mono alphabet count width) tuples increase

/-- Additional original tuples retain each shorter sequence. -/
theorem tupleSchedule_count_mono (alphabet : List Guard) (count width : Nat)
    {first last : Nat} (increase : first ≤ last) (resource : Nat) :
    tupleSchedule alphabet count width first resource ≤ tupleSchedule alphabet count width last resource :=
  SourceCurrentMemoMergeNumericControl.iterate_count_mono _
    (SourceCurrentConjunctionTupleNumeric.forecast_ge alphabet count width) increase resource

/-- Exposure fixes the row width before the original Cartesian tuple scan starts. -/
noncomputable def forecast (alphabet : List Guard) (count resource : Nat) : Nat :=
  let width := SourceCurrentConjunctionExposureResources.forecast count resource
  tupleSchedule alphabet count width (width ^ count) width

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem tuples_exact {tuples : List (List (EdgeValue Symbol Guard))}
    {before after : Physical} {rows : List (List (List (Value Symbol Guard)))}
    (actual : Tuples tuples before rows after) (alphabet : List Guard) (count width resource : Nat)
    (ready : Ready before) (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple) (fits : Fits resource before.heap)
    (counts : ∀ tuple ∈ tuples, tuple.length ≤ count)
    (widths : ∀ tuple ∈ tuples, ∀ edge ∈ tuple, edge.children.length ≤ width)
    (carrier : ∀ tuple ∈ tuples, ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet) :
    Fits (tupleSchedule alphabet count width tuples.length resource) after.heap ∧ rows.length ≤ tuples.length ∧
      (∀ row ∈ rows, row.length ≤ width + shapeThrough alphabet count ∧
        ∀ requirement ∈ row, requirement.length ≤ count + count * shapeThrough alphabet count) ∧
      (∀ work reader, workerFuel (shapeThrough alphabet count) ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (tupleSchedule alphabet count width tuples.length resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.tuples work reader tuples before = .done rows after) := by
  induction actual generalizing resource with
  | nil => exact ⟨fits, Nat.le_refl _, by simp, by intros; rfl⟩
  | @skip tuple before middle tuples rows after first rest ih =>
      have own := SourceCurrentConjunctionTupleNumeric.bound first alphabet count width resource ready
        (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self) fits
        (counts tuple List.mem_cons_self) (widths tuple List.mem_cons_self) (carrier tuple List.mem_cons_self)
      have later := ih (SourceCurrentConjunctionTupleNumeric.forecast alphabet count width resource) own.1.ready
        (fun selected member edge included => edge_grows before.heap middle.heap own.1.keeps.growth edge
          (resident selected (List.mem_cons_of_mem _ member) edge included))
        (fun selected member => closed selected (List.mem_cons_of_mem _ member)) own.2.2.1
        (fun selected member => counts selected (List.mem_cons_of_mem _ member))
        (fun selected member => widths selected (List.mem_cons_of_mem _ member))
        (fun selected member => carrier selected (List.mem_cons_of_mem _ member))
      have larger := tupleSchedule_ge alphabet count width tuples.length
        (SourceCurrentConjunctionTupleNumeric.forecast alphabet count width resource)
      refine ⟨later.1, by have own := later.2.1; simp only [List.length_cons]; omega, later.2.2.1, ?_⟩
      intro work reader enoughWork enoughRead
      have firstDone := own.2.2.2.2 work reader enoughWork
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono larger) enoughRead)
      have tailDone := later.2.2.2 work reader enoughWork enoughRead
      simp only [SourceCurrentConjunctionRowsWorker.tuples, firstDone, tailDone,
        SourceCurrentConjunctionRowsWorker.Outcome.bind]
  | @keep tuple before row middle tuples rows after first rest ih =>
      have own := SourceCurrentConjunctionTupleNumeric.bound first alphabet count width resource ready
        (resident tuple List.mem_cons_self) (closed tuple List.mem_cons_self) fits
        (counts tuple List.mem_cons_self) (widths tuple List.mem_cons_self) (carrier tuple List.mem_cons_self)
      have later := ih (SourceCurrentConjunctionTupleNumeric.forecast alphabet count width resource) own.1.ready
        (fun selected member edge included => edge_grows before.heap middle.heap own.1.keeps.growth edge
          (resident selected (List.mem_cons_of_mem _ member) edge included))
        (fun selected member => closed selected (List.mem_cons_of_mem _ member)) own.2.2.1
        (fun selected member => counts selected (List.mem_cons_of_mem _ member))
        (fun selected member => widths selected (List.mem_cons_of_mem _ member))
        (fun selected member => carrier selected (List.mem_cons_of_mem _ member))
      have larger := tupleSchedule_ge alphabet count width tuples.length
        (SourceCurrentConjunctionTupleNumeric.forecast alphabet count width resource)
      refine ⟨later.1, by have own := later.2.1; simp only [List.length_cons]; omega, ?_, ?_⟩
      · intro selected member
        rcases List.mem_cons.mp member with rfl | member
        · exact own.2.2.2.1
        · exact later.2.2.1 selected member
      · intro work reader enoughWork enoughRead
        have firstDone := own.2.2.2.2 work reader enoughWork
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono larger) enoughRead)
        have tailDone := later.2.2.2 work reader enoughWork enoughRead
        simp only [SourceCurrentConjunctionRowsWorker.tuples, firstDone, tailDone,
          SourceCurrentConjunctionRowsWorker.Outcome.bind]

/-- A count fixed before tuple processing bounds the same complete actual tuple list. -/
theorem tuples_bound {tuples : List (List (EdgeValue Symbol Guard))}
    {before after : Physical} {rows : List (List (List (Value Symbol Guard)))}
    (actual : Tuples tuples before rows after) (alphabet : List Guard) (count width tupleCount resource : Nat)
    (ready : Ready before) (resident : ∀ tuple ∈ tuples, Edges before.heap tuple)
    (closed : ∀ tuple ∈ tuples, ClosedEdges tuple) (fits : Fits resource before.heap)
    (counts : ∀ tuple ∈ tuples, tuple.length ≤ count)
    (widths : ∀ tuple ∈ tuples, ∀ edge ∈ tuple, edge.children.length ≤ width)
    (carrier : ∀ tuple ∈ tuples, ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet)
    (length : tuples.length ≤ tupleCount) :
    Fits (tupleSchedule alphabet count width tupleCount resource) after.heap ∧ rows.length ≤ tupleCount ∧
      (∀ row ∈ rows, row.length ≤ width + shapeThrough alphabet count ∧
        ∀ requirement ∈ row, requirement.length ≤ count + count * shapeThrough alphabet count) ∧
      (∀ work reader, workerFuel (shapeThrough alphabet count) ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (tupleSchedule alphabet count width tupleCount resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.tuples work reader tuples before = .done rows after) := by
  have own := tuples_exact actual alphabet count width resource ready resident closed fits counts widths carrier
  have larger := tupleSchedule_count_mono alphabet count width length resource
  exact ⟨own.1.mono larger, Nat.le_trans own.2.1 length, own.2.2.1,
    fun work reader enoughWork enoughRead => own.2.2.2 work reader enoughWork
      (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono larger) enoughRead)⟩

end MicroCFTA.SourceCurrentConjunctionRowsResources
