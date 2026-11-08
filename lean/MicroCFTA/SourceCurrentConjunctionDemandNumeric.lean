import MicroCFTA.SourceCurrentConjunctionDemandExecution
import MicroCFTA.SourceCurrentConjunctionTuplePullNumeric
import MicroCFTA.SourceCurrentConjunctionTupleWorklistResources

/-!
# Initial numeric bounds for demanded admission

The original budget enlarges the initial scalar by a maximum. A fitting
sample has at most that many tuples. The existing row schedule therefore
bounds the actual sampled tuple allocation. No future tuple count is an
input. Computed sample completion and successful stability identify the
same actual sample before replay of the tuple worker.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready Effects Tuples)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionDemandExecution (Admission)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "step" => SourceCurrentConjunctionWorklistResources.step
local notation "projectionFuel" => SourceCurrentConjunctionProjectionResources.workerFuel
local notation "readFuel" => SourceCurrentProjectionUnionResources.readFuel
local notation "exposure" => SourceCurrentConjunctionExposureResources.forecast
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap

/-- The original scalar and raw budget determine one initial scalar. -/
def seed (resource budget : Nat) : Nat := max resource budget

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem sample_bound {h budget : Nat} {nodes : List Node}
    {before after : Physical Symbol Formula} {result : SourceCurrentConjunctionTuplePullTotal.Result Symbol Formula}
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (fits : Fits resource before.heap)
    (known : AnnotationHeap (fun guard => guard ∈ alphabet) before.heap) :
    Effects before after ∧ AnnotationHeap (fun guard => guard ∈ alphabet) after.heap ∧
      Fits (exposure nodes.length resource) after.heap ∧
      ∀ H, SourceCurrentConjunctionTuplePullNumeric.fuel nodes.length resource ≤ H →
        SourceCurrentConjunctionTuplePullTotal.sample H budget nodes before = .done result after := by
  obtain ⟨selected, final, completed, effects, _supported, _bounded, _closed, boundedHeap⟩ :=
    SourceCurrentConjunctionTuplePullNumeric.sample_complete budget nodes before resource ready available closed fits
  have observed := SourceCurrentConjunctionTuplePullStability.sample_done_stable actual
    (Nat.le_max_left h (SourceCurrentConjunctionTuplePullNumeric.fuel nodes.length resource))
  have computed := completed (max h (SourceCurrentConjunctionTuplePullNumeric.fuel nodes.length resource))
    (Nat.le_max_right _ _)
  have same := observed.symm.trans computed
  have selectedSame : selected = result := (Outcome.done.inj same).1.symm
  have finalSame : final = after := (Outcome.done.inj same).2.symm
  rw [selectedSame, finalSame] at completed
  rw [finalSame] at effects boundedHeap
  obtain ⟨demands, rows, reads, included⟩ :=
    SourceCurrentConjunctionTuplePullReadTrace.sample_reads h budget nodes before after result actual
  have guards := reads.verified (fun guard => guard ∈ alphabet) ready.semantic ready.costs known
    (fun value member => available value (included value member))
    (fun value member => closed value (included value member))
  exact ⟨effects, guards.1.annotations, boundedHeap, completed⟩

private theorem fitting_bound {h budget : Nat} {nodes : List Node}
    {before middle after : Physical Symbol Formula} {tuples : List (List Edge)}
    {requirements : List (List (List Node))}
    (sampled : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.fit tuples) middle)
    (allocated : Tuples tuples middle requirements after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (fits : Fits resource before.heap)
    (length : nodes.length ≤ resource) (known : AnnotationHeap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (step alphabet (seed resource budget)) after.heap ∧ requirements.length ≤ tuples.length ∧
      (∀ row ∈ requirements,
        row.length ≤ exposure (seed resource budget) (seed resource budget + 1) + shapeThrough alphabet (seed resource budget) ∧
        ∀ requirement ∈ row,
          requirement.length ≤ seed resource budget + seed resource budget * shapeThrough alphabet (seed resource budget)) ∧
      ∀ p H, projectionFuel (shapeThrough alphabet (seed resource budget)) ≤ p →
        readFuel (step alphabet (seed resource budget)) ≤ H →
        SourceCurrentConjunctionRowsWorker.tuples p H tuples middle = .done requirements after := by
  let count := seed resource budget
  let width := exposure count (count + 1)
  have original : resource ≤ count := Nat.le_max_left _ _
  have budgetLe : budget ≤ count := Nat.le_max_right _ _
  have positive : 1 ≤ count := Nat.le_trans fits.stored.positive original
  have widthLe : count + 1 ≤ width := SourceCurrentConjunctionExposureResources.forecast_ge _ _
  have raw := sample_bound sampled alphabet resource ready available closed fits known
  have bounded : Fits width middle.heap := raw.2.2.1.mono
    (SourceCurrentConjunctionExposureResources.forecast_mono (Nat.le_trans length original) (by omega))
  have supported := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h budget nodes before ready available
  have resident : ∀ tuple ∈ tuples, Edges middle.heap tuple :=
    supported.2 (.fit tuples) middle sampled
  have closedTuples : ∀ tuple ∈ tuples, ClosedEdges tuple :=
    (SourceCurrentConjunctionTuplePullClosedSample.sample_closed h budget nodes before ready available closed).2
      (.fit tuples) middle sampled
  have counts : ∀ tuple ∈ tuples, tuple.length ≤ count := by
    intro tuple member
    rw [(SourceCurrentConjunctionTuplePullShapes.sample_fit h budget nodes before middle tuples sampled tuple member).1]
    exact Nat.le_trans length original
  have widths : ∀ tuple ∈ tuples, ∀ edge ∈ tuple, edge.children.length ≤ width := by
    intro tuple member edge included
    have small := InternedValueMassHeap.resident middle.heap bounded.stored edge (resident tuple member edge included)
    have children := InternedStoredEncodingWidth.values_length edge.children
    rw [InternedValueMass.edge_children] at small
    omega
  have carrier : ∀ tuple ∈ tuples, ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet :=
    fun tuple member edge included => raw.2.1 edge.entry.key edge (resident tuple member edge included)
  have sampleCount : tuples.length ≤ budget :=
    SourceCurrentConjunctionTuplePullTotal.sample_bounded h budget nodes before middle (.fit tuples) sampled
  have power : count ≤ width ^ count := by
    have enough := Nat.pow_le_pow_right (by omega : 1 ≤ width) positive
    simp only [Nat.pow_one] at enough
    exact Nat.le_trans (by omega : count ≤ width) enough
  have tupleCount : tuples.length ≤ width ^ count := Nat.le_trans sampleCount (Nat.le_trans budgetLe power)
  have numeric := SourceCurrentConjunctionRowsResources.tuples_bound allocated alphabet count width tuples.length width
    raw.1.ready resident closedTuples bounded counts widths carrier (Nat.le_refl _)
  have schedule : SourceCurrentConjunctionRowsResources.tupleSchedule alphabet count width tuples.length width ≤
      step alphabet count := SourceCurrentConjunctionRowsResources.tupleSchedule_count_mono alphabet count width tupleCount width
  refine ⟨numeric.1.mono schedule, numeric.2.1, numeric.2.2.1, ?_⟩
  intro p H enoughP enoughH
  exact numeric.2.2.2 p H enoughP
    (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono schedule) enoughH)

/-- One original scalar and budget bound the same actual admission and its exact stable replay. -/
theorem bound {budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) (alphabet : List Guard) (resource : Nat)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (fits : Fits resource before.heap) (length : nodes.length ≤ resource)
    (known : AnnotationHeap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (step alphabet (seed resource budget)) after.heap ∧
      ∀ p h, projectionFuel (shapeThrough alphabet (seed resource budget)) ≤ p →
        readFuel (step alphabet (seed resource budget)) ≤ h →
        SourceCurrentConjunctionDemandAdmission.run p h budget nodes before = .done result after := by
  have original : resource ≤ seed resource budget := Nat.le_max_left _ _
  have exposed : exposure nodes.length resource ≤ step alphabet (seed resource budget) :=
    Nat.le_trans (SourceCurrentConjunctionExposureResources.forecast_mono (Nat.le_trans length original)
      (Nat.le_trans original (Nat.le_succ _)))
      (SourceCurrentConjunctionRowsResources.tupleSchedule_ge alphabet (seed resource budget) _ _ _)
  cases actual with
  | overflow sampled =>
      have numeric := sample_bound sampled alphabet resource ready available closed fits known
      refine ⟨numeric.2.2.1.mono exposed, ?_⟩
      intro p h _ enoughH
      exact SourceCurrentConjunctionDemandAdmission.run_overflow p h _ _ _ _ _ _
        (numeric.2.2.2 h (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono exposed) enoughH))
  | zero sampled =>
      have numeric := sample_bound sampled alphabet resource ready available closed fits known
      refine ⟨numeric.2.2.1.mono exposed, ?_⟩
      intro p h _ enoughH
      exact SourceCurrentConjunctionDemandAdmission.run_zero p h _ _ _ _
        (numeric.2.2.2 h (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono exposed) enoughH))
  | positive sampled allocated =>
      have numeric := fitting_bound sampled allocated alphabet resource ready available closed fits length known
      have first := sample_bound sampled alphabet resource ready available closed fits known
      refine ⟨numeric.1, ?_⟩
      intro p h enoughP enoughH
      exact SourceCurrentConjunctionDemandAdmission.run_positive p h _ _ _ _ _ _ _ _
        (first.2.2.2 h (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono exposed) enoughH))
        (numeric.2.2.2 p h enoughP enoughH)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem flatten_length_le {A : Type} (rows : List (List A)) (width : Nat)
    (bounded : ∀ row ∈ rows, row.length ≤ width) : rows.flatten.length ≤ rows.length * width := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have first := bounded row List.mem_cons_self
      have later := ih (fun values member => bounded values (List.mem_cons_of_mem _ member))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The actual positive charge bounds every newly prepended requirement after demand sampling. -/
theorem positive_generated {budget predecessor : Nat} {nodes : List Node}
    {before after : Physical Symbol Formula} {requirements : List (List (List Node))}
    (actual : Admission budget nodes before (.positive predecessor requirements) after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (fits : Fits resource before.heap)
    (length : nodes.length ≤ resource) (known : AnnotationHeap (fun guard => guard ∈ alphabet) before.heap) :
    requirements.flatten.length ≤ (predecessor + 1) *
      SourceCurrentConjunctionTupleWorklistResources.rowWidth alphabet (step alphabet (seed resource budget)) := by
  cases actual with
  | positive sampled allocated =>
      have numeric := fitting_bound sampled allocated alphabet resource ready available closed fits length known
      have widthLe : exposure (seed resource budget) (seed resource budget + 1) ≤ step alphabet (seed resource budget) :=
        SourceCurrentConjunctionRowsResources.tupleSchedule_ge alphabet (seed resource budget) _ _ _
      have resourceLe : seed resource budget ≤ step alphabet (seed resource budget) :=
        Nat.le_trans (Nat.le_succ _) (SourceCurrentConjunctionWorklistResources.step_ge _ _)
      have rows := flatten_length_le requirements
        (SourceCurrentConjunctionTupleWorklistResources.rowWidth alphabet (step alphabet (seed resource budget)))
        (fun row member => Nat.le_trans (numeric.2.2.1 row member).1
          (Nat.add_le_add widthLe (SourceCurrentConjunctionTupleBounds.shapeThrough_mono alphabet resourceLe)))
      exact Nat.le_trans rows (Nat.mul_le_mul_right _ (by simpa only [List.length_cons] using numeric.2.1))

end MicroCFTA.SourceCurrentConjunctionDemandNumeric
