import MicroCFTA.SourceCurrentMemoMergeResourceControl
import MicroCFTA.SourceCurrentAllocatedRowReadUniform
import MicroCFTA.SourceCurrentAllocatedProjectionResources
import MicroCFTA.SourceEqualityProjectionWorkerComplete

/-!
# Initial scalar bounds for actual projection reads and unions

A uniform initial reader fuel fixes the exact returned heap. Its explicit
read schedule bounds the literal returned row count. Ordered scans retain
all earlier heaps in an increasing scalar envelope. Node work uses the
proved row count and the actual store, including earlier cached winners.
-/
namespace MicroCFTA.SourceCurrentProjectionUnionResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits primitiveGrowth)
open SourceCurrentMemoMergeEffects (Effect)
open SourceCurrentAllocatedRecursiveMassTrace (massAfter)
open SourceCurrentAllocatedReaderControl (g)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- One initial scalar fixes a complete recursive row-read fuel. -/
def readFuel (bound : Nat) : Nat := SourceCurrentAllocatedRowReadNumeric.readFuel bound bound bound
/-- The explicit read schedule bounds the literal output row count. -/
def readWidth (bound : Nat) : Nat := (readFuel bound + 1) * massAfter (readFuel bound + 1) bound
/-- One initial scalar covers both the returned heap and its row count. -/
def readGrowth (bound : Nat) : Nat := bound + readFuel bound + readWidth bound
/-- Head normalization pays the final actual node constructor. -/
def headGrowth (bound : Nat) : Nat := primitiveGrowth (readWidth bound) (readGrowth bound)
/-- Ordered scans start each read at the exact preceding heap. -/
def readAllGrowth : Nat → Nat → Nat
  | 0, bound => bound
  | count + 1, bound => readAllGrowth count (readGrowth bound)
/-- Source union pays one node for the complete concatenated row list. -/
def unionGrowth (count bound : Nat) : Nat :=
  primitiveGrowth (count * readAllGrowth count bound) (readAllGrowth count bound)

/-- Larger initial resources retain the diagonal reader fuel. -/
theorem readFuel_mono {first last : Nat} (increase : first ≤ last) : readFuel first ≤ readFuel last := by
  unfold readFuel SourceCurrentAllocatedRowReadNumeric.readFuel SourceCurrentAllocatedReaderNumeric.fuel
  apply HeightOrderControlled.majorant_joint_mono g SourceCurrentAllocatedReaderControl.g_mono
    SourceCurrentAllocatedReaderControl.g_strict (Nat.add_le_add_right increase 1)
  apply SourceCurrentAllocatedReaderControl.g_mono
  unfold SourceCurrentAllocatedReaderNumeric.initialControl
  simp only [Nat.one_mul]
  omega
/-- Larger initial resources retain the row-count bound. -/
theorem readWidth_mono {first last : Nat} (increase : first ≤ last) : readWidth first ≤ readWidth last := by
  have fuel := Nat.add_le_add_right (readFuel_mono increase) 1
  exact Nat.mul_le_mul fuel (SourceCurrentAllocatedRecursiveMassMonotone.massAfter_mono fuel increase)
/-- Row reads retain their initial scalar bound. -/
theorem readGrowth_ge (bound : Nat) : bound ≤ readGrowth bound := by unfold readGrowth; omega
/-- The row-read envelope includes its literal output width. -/
theorem readWidth_le_growth (bound : Nat) : readWidth bound ≤ readGrowth bound := by unfold readGrowth; omega
/-- Larger initial resources retain the row-read envelope. -/
theorem readGrowth_mono {first last : Nat} (increase : first ≤ last) : readGrowth first ≤ readGrowth last :=
  Nat.add_le_add (Nat.add_le_add increase (readFuel_mono increase)) (readWidth_mono increase)
/-- Head normalization retains its initial scalar bound. -/
theorem headGrowth_ge (bound : Nat) : bound ≤ headGrowth bound :=
  Nat.le_trans (readGrowth_ge bound) (SourceCurrentMemoMergeResourceControl.primitiveGrowth_ge _ _)
/-- Larger initial resources retain the head envelope. -/
theorem headGrowth_mono {first last : Nat} (increase : first ≤ last) : headGrowth first ≤ headGrowth last :=
  SourceCurrentMemoMergeResourceControl.primitiveGrowth_mono (readWidth_mono increase) (readGrowth_mono increase)
/-- An ordered scan retains its initial scalar bound. -/
theorem readAllGrowth_ge (count bound : Nat) : bound ≤ readAllGrowth count bound := by
  induction count generalizing bound with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (readGrowth_ge bound) (ih _)
/-- A fixed scan retains larger initial resources. -/
theorem readAllGrowth_bound_mono (count : Nat) {first last : Nat} (increase : first ≤ last) :
    readAllGrowth count first ≤ readAllGrowth count last := by
  induction count generalizing first last with
  | zero => exact increase
  | succ count ih => exact ih (readGrowth_mono increase)
/-- Additional operands retain the earlier scan envelope. -/
theorem readAllGrowth_count_mono {first last : Nat} (increase : first ≤ last) (bound : Nat) :
    readAllGrowth first bound ≤ readAllGrowth last bound := by
  induction increase with
  | refl => exact Nat.le_refl _
  | @step last increase ih =>
      exact Nat.le_trans ih (readAllGrowth_bound_mono last (readGrowth_ge bound))
/-- Larger counts and initial resources retain the scan envelope. -/
theorem readAllGrowth_mono {firstCount lastCount firstBound lastBound : Nat}
    (counts : firstCount ≤ lastCount) (bounds : firstBound ≤ lastBound) :
    readAllGrowth firstCount firstBound ≤ readAllGrowth lastCount lastBound :=
  Nat.le_trans (readAllGrowth_count_mono counts firstBound) (readAllGrowth_bound_mono lastCount bounds)
/-- Source union retains its initial scalar bound. -/
theorem unionGrowth_ge (count bound : Nat) : bound ≤ unionGrowth count bound :=
  Nat.le_trans (readAllGrowth_ge count bound) (SourceCurrentMemoMergeResourceControl.primitiveGrowth_ge _ _)
/-- Larger counts and initial resources retain the union envelope. -/
theorem unionGrowth_mono {firstCount lastCount firstBound lastBound : Nat}
    (counts : firstCount ≤ lastCount) (bounds : firstBound ≤ lastBound) :
    unionGrowth firstCount firstBound ≤ unionGrowth lastCount lastBound := by
  have scan := readAllGrowth_mono counts bounds
  exact SourceCurrentMemoMergeResourceControl.primitiveGrowth_mono (Nat.mul_le_mul counts scan) scan

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual read derives both a current-heap bound and a finite literal output width. -/
theorem read {value : Value Symbol Guard} {before after : State Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)} (actual : SourceEqualityProjectionRead.Read value before rows after)
    (bound : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (closed : value.free = []) (fits : Fits bound before) :
    Effect before after ∧ Fits (readGrowth bound) after ∧ rows.length ≤ readWidth bound ∧
      Edges after rows ∧ ClosedEdges rows ∧
      MergedFreshOrdinaryExposure.nodeEdges (readFuel bound) value before = .done rows after ∧
      ∀ extra, MergedFreshOrdinaryExposure.nodeEdges (readFuel bound + extra) value before = .done rows after := by
  have replay := SourceCurrentAllocatedRowReadUniform.of_read actual bound semantic available closed fits.stored fits.nodes fits.edges
  have width := SourceCurrentAllocatedProjectionResources.read_bound (readFuel bound) value before
    semantic.ready.semantic semantic.ready.covered available closed bound fits.stored rows after replay.1
  have physical := SourceEqualityExposureCosts.nodeEdges_verified (readFuel bound) value before semantic costs available
  have effect : Effect before after := by
    refine ⟨?_, replay.2.2.1, ?_⟩
    · have kept := physical.keeps
      rw [replay.1] at kept
      exact kept
    · have retained := physical.costs
      rw [replay.1] at retained
      exact retained
  have enough : readFuel bound ≤ readGrowth bound := by unfold readGrowth; omega
  refine ⟨effect, ⟨replay.2.2.2.1.mono enough, Nat.le_trans replay.2.2.2.2.1 enough,
    Nat.le_trans replay.2.2.2.2.2.1 enough, Nat.zero_le _⟩, width.2.2.2.1,
    replay.2.2.2.2.2.2.1, replay.2.2.2.2.2.2.2.1, replay.1, replay.2.2.2.2.2.2.2.2⟩

end Actual
end MicroCFTA.SourceCurrentProjectionUnionResources
