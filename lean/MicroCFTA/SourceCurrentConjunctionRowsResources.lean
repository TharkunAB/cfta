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

/-- Larger original tuple dimensions and counts retain the complete sequence. -/
theorem tupleSchedule_limits_mono (alphabet : List Guard)
    {firstCount lastCount firstWidth lastWidth firstTuples lastTuples : Nat}
    (counts : firstCount ≤ lastCount) (widths : firstWidth ≤ lastWidth)
    (tuples : firstTuples ≤ lastTuples) (resource : Nat) :
    tupleSchedule alphabet firstCount firstWidth firstTuples resource ≤
      tupleSchedule alphabet lastCount lastWidth lastTuples resource := by
  have same := SourceCurrentMemoMergeNumericControl.iterate_compare _ _
    (SourceCurrentConjunctionTupleNumeric.forecast_mono alphabet lastCount lastWidth)
    (SourceCurrentConjunctionTupleNumeric.forecast_limits_mono alphabet counts widths)
    firstTuples (Nat.le_refl resource)
  exact Nat.le_trans same (tupleSchedule_count_mono alphabet lastCount lastWidth tuples resource)

/-- Exposure fixes the row width before the original Cartesian tuple scan starts. -/
noncomputable def forecast (alphabet : List Guard) (count resource : Nat) : Nat :=
  let width := SourceCurrentConjunctionExposureResources.forecast count resource
  tupleSchedule alphabet count width (width ^ count) width

/-- The complete row schedule retains its initial heap scalar. -/
theorem forecast_ge (alphabet : List Guard) (count resource : Nat) : resource ≤ forecast alphabet count resource :=
  Nat.le_trans (SourceCurrentConjunctionExposureResources.forecast_ge count resource)
    (tupleSchedule_ge alphabet count _ _ _)

/-- Positive larger initial resources and counts retain the full row envelope. -/
theorem forecast_mono (alphabet : List Guard) {firstCount lastCount firstResource lastResource : Nat}
    (counts : firstCount ≤ lastCount) (resources : firstResource ≤ lastResource) (positive : 1 ≤ lastResource) :
    forecast alphabet firstCount firstResource ≤ forecast alphabet lastCount lastResource := by
  have widths := SourceCurrentConjunctionExposureResources.forecast_mono counts resources
  have widthPositive := Nat.le_trans positive (SourceCurrentConjunctionExposureResources.forecast_ge lastCount lastResource)
  have powers := Nat.le_trans (Nat.pow_le_pow_left widths firstCount) (Nat.pow_le_pow_right widthPositive counts)
  exact Nat.le_trans (tupleSchedule_mono alphabet firstCount _ _ widths)
    (tupleSchedule_limits_mono alphabet counts widths powers _)

/-- A positive original scalar reserves enough space for every generated pending operand list. -/
theorem pending_width (alphabet : List Guard) (count resource : Nat) (positive : 1 ≤ resource) :
    count + count * shapeThrough alphabet count ≤ forecast alphabet count resource := by
  let width := SourceCurrentConjunctionExposureResources.forecast count resource
  have widthPositive : 1 ≤ width := Nat.le_trans positive (SourceCurrentConjunctionExposureResources.forecast_ge _ _)
  have power : 0 < width ^ count := Nat.pow_pos (by omega)
  have one := tupleSchedule_count_mono alphabet count width (by omega : 1 ≤ width ^ count) width
  change SourceCurrentConjunctionTupleNumeric.forecast alphabet count width width ≤ forecast alphabet count resource at one
  exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) one

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

variable [DecidableEq Symbol]

/-- Initial operand and guard-carrier bounds control the same complete actual row graph. -/
theorem bound {nodes : List (Value Symbol Guard)} {before after : Physical}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Rows nodes before rows after)
    (alphabet : List Guard) (count resource : Nat) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (fits : Fits resource before.heap)
    (length : nodes.length ≤ count)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet count resource) after.heap ∧
      (∀ row ∈ rows, ∀ requirement ∈ row, requirement.length ≤ forecast alphabet count resource) ∧
      (∀ work reader, workerFuel (shapeThrough alphabet count) ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (forecast alphabet count resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.rows work reader nodes before = .done rows after) := by
  cases actual with
  | @run edges heap rows after before reads tuples =>
      let width := SourceCurrentConjunctionExposureResources.forecast count resource
      have exposed := SourceCurrentConjunctionExposureResources.bounded reads count resource
        ready.semantic ready.costs available closed fits length
      have effects := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
        ready.semantic ready.costs ready.fields available closed
      have guards := reads.verified (fun guard => guard ∈ alphabet)
        ready.semantic ready.costs known available closed
      have middle : Ready (⟨heap, before.equality⟩ : Physical) :=
        ⟨effects.1.semantic, effects.1.costs, ready.valid, effects.1.annotations⟩
      have resident : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges, Edges heap tuple :=
        fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified (fun guard => guard ∈ alphabet)
          reads ready.semantic ready.costs known available closed tuple member).2.1
      have noFree : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges, ClosedEdges tuple :=
        fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified (fun guard => guard ∈ alphabet)
          reads ready.semantic ready.costs known available closed tuple member).2.2
      have counts : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges, tuple.length ≤ count := by
        intro tuple member
        rw [SourceCurrentConjunctionTupleBounds.tuple_length edges tuple member, exposed.2.1]
        exact length
      have widths : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges,
          ∀ edge ∈ tuple, edge.children.length ≤ width := by
        intro tuple member edge included
        have small := InternedValueMassHeap.resident heap exposed.1.stored edge (resident tuple member edge included)
        have children := InternedStoredEncodingWidth.values_length edge.children
        rw [InternedValueMass.edge_children] at small
        omega
      have carrier : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges,
          ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet :=
        fun tuple member edge included => guards.1.annotations edge.entry.key edge (resident tuple member edge included)
      have widthPositive : 1 ≤ width := Nat.le_trans fits.stored.positive
        (SourceCurrentConjunctionExposureResources.forecast_ge count resource)
      have tupleCount : (SourceCurrentConjunctionTuples.tuples edges).length ≤ width ^ count := by
        have own := SourceCurrentConjunctionTupleBounds.tuples_length_le edges width exposed.2.2.1
        have count : edges.length ≤ count := by rw [exposed.2.1]; exact length
        exact Nat.le_trans own (Nat.pow_le_pow_right widthPositive count)
      have later := tuples_bound tuples alphabet count width (width ^ count) width middle resident noFree
        exposed.1 counts widths carrier tupleCount
      have retained : width ≤ forecast alphabet count resource := tupleSchedule_ge alphabet count width _ width
      refine ⟨later.1, ?_, ?_⟩
      · intro row member requirement included
        exact Nat.le_trans ((later.2.2.1 row member).2 requirement included)
          (pending_width alphabet count resource fits.stored.positive)
      · intro work reader enoughWork enoughRead
        have firstDone := exposed.2.2.2 before.equality reader
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono retained) enoughRead)
        have tailDone := later.2.2.2 work reader enoughWork enoughRead
        simp only [SourceCurrentConjunctionRowsWorker.rows, firstDone, tailDone,
          SourceCurrentConjunctionRowsWorker.Outcome.bind]

/-- Original physical facts construct the complete numeric row return and retained guard carrier. -/
theorem complete (nodes : List (Value Symbol Guard)) (before : Physical)
    (alphabet : List Guard) (count resource : Nat) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (fits : Fits resource before.heap)
    (length : nodes.length ≤ count)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    ∃ rows after, Rows nodes before rows after ∧ Effects before after ∧ RowsReady after rows ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.heap ∧
      Fits (forecast alphabet count resource) after.heap ∧
      (∀ row ∈ rows, ∀ requirement ∈ row, requirement.length ≤ forecast alphabet count resource) ∧
      (∀ work reader, workerFuel (shapeThrough alphabet count) ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (forecast alphabet count resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.rows work reader nodes before = .done rows after) := by
  obtain ⟨rows, after, actual, _, _⟩ :=
    SourceCurrentConjunctionRowsAllocation.rows_complete nodes before ready available closed
  have physical := SourceCurrentConjunctionGuardUniverse.rows_heap (fun guard => guard ∈ alphabet)
    actual ready available closed known
  have own := bound actual alphabet count resource ready available closed fits length known
  exact ⟨rows, after, actual, physical.1, physical.2.2, physical.2.1, own⟩

end MicroCFTA.SourceCurrentConjunctionRowsResources
