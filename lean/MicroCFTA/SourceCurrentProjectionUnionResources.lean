import MicroCFTA.SourceCurrentMemoMergeResourceControl
import MicroCFTA.SourceCurrentAllocatedRowReadUniform
import MicroCFTA.SourceCurrentAllocatedProjectionResources
import MicroCFTA.SourceCurrentProjectionNumericReplay

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
  have done : MergedFreshOrdinaryExposure.nodeEdges (readFuel bound) value before = .done rows after := replay.1
  have width := SourceCurrentAllocatedProjectionResources.read_bound (readFuel bound) value before
    semantic.ready.semantic semantic.ready.covered available closed bound fits.stored rows after replay.1
  have physical := SourceEqualityExposureCosts.nodeEdges_verified (readFuel bound) value before semantic costs available
  have effect : Effect before after := by
    refine ⟨?_, replay.2.2.1, ?_⟩
    · have kept := physical.keeps
      rw [done] at kept
      exact kept
    · have retained := physical.costs
      rw [done] at retained
      exact retained
  have enough : readFuel bound ≤ readGrowth bound := by unfold readGrowth; omega
  refine ⟨effect, ⟨replay.2.2.2.1.mono enough, Nat.le_trans replay.2.2.2.2.1 enough,
    Nat.le_trans replay.2.2.2.2.2.1 enough, Nat.zero_le _⟩, width.2.2.2.1,
    replay.2.2.2.2.2.2.1, replay.2.2.2.2.2.2.2.1, replay.1, replay.2.2.2.2.2.2.2.2⟩

/-- Exact earlier row reads remain ready at every larger initial scalar envelope. -/
theorem read_ready {value : Value Symbol Guard} {before after : State Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)} (actual : SourceEqualityProjectionRead.Read value before rows after)
    (bound larger : Nat) (semantic : SemanticReady before) (available : Available before value)
    (closed : value.free = []) (fits : Fits bound before) (increase : bound ≤ larger) :
    SourceCurrentProjectionNumericReplay.ReadReady (readFuel larger) actual := by
  have wide := SourceCurrentMemoMergeResourceControl.Fits.mono fits increase
  exact (SourceCurrentAllocatedRowReadUniform.of_read actual larger semantic available closed wide.stored wide.nodes wide.edges).1

/-- An actual head read pays its final node and retains the exact shared read certificate. -/
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (bound : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (closed : value.free = []) (fits : Fits bound before) :
    Effect before after ∧ Fits (headGrowth bound) after ∧ Available after result ∧ result.free = [] ∧
      SourceCurrentProjectionNumericReplay.HeadReady (readFuel (headGrowth bound)) actual := by
  cases actual with
  | read fuel rows middle exposed rebuilt =>
      have first := read (.done fuel exposed) bound semantic costs available closed fits
      have final := SourceEqualityRequiredCache.node rows middle first.1.semantic.ready first.2.2.2.1 first.2.2.2.2.1
      have finalEffect : Effect middle (run (makeNode rows) middle).2 :=
        ⟨final.1, SourceEqualityRequiredSemanticCache.node rows middle first.1.semantic first.2.2.2.1 first.2.2.2.2.1,
          InternedFreshOrdinaryCostHeap.preserve middle _ first.1.costs (InternedShallowHeap.makeNode_noNewMu rows middle)⟩
      have resources := SourceCurrentMemoMergeResourceControl.node rows middle (readGrowth bound) (readWidth bound)
        first.2.1 first.2.2.2.1 first.2.2.1
      have ready := read_ready (.done fuel exposed) bound (headGrowth bound) semantic available closed fits (headGrowth_ge bound)
      have ordinary := (SourceEqualityRequiredHead.Head.verified
        (.read fuel rows middle exposed rebuilt) semantic.ready available closed).2.2.2
      have resultSame := congrArg Prod.fst rebuilt
      have stateSame := congrArg Prod.snd rebuilt
      dsimp only at resultSame stateSame
      subst result
      subst after
      exact ⟨first.1.trans finalEffect, resources.1, final.2.1, final.2.2.1,
        .read fuel rows middle exposed rfl ready ordinary⟩

private theorem readAll_exact {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)} (actual : SourceEqualityProjectionUnion.ReadAll values before rows after)
    (bound : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (fits : Fits bound before) :
    Effect before after ∧ Fits (readAllGrowth values.length bound) after ∧
      rows.length ≤ values.length * readAllGrowth values.length bound ∧
      SourceCurrentProjectionNumericReplay.ReadAllReady (readFuel (readAllGrowth values.length bound)) actual := by
  induction actual generalizing bound with
  | nil => exact ⟨SourceCurrentMemoMergeEffects.effect_refl _ semantic costs, fits, Nat.zero_le _, .nil _⟩
  | @cons value before own middle values more after first rest ih =>
      have head := read first bound semantic costs (available value List.mem_cons_self) (closed value List.mem_cons_self) fits
      have tail := ih (readGrowth bound) head.1.semantic head.1.costs
        (fun value member => head.1.keeps.available _ (available value (List.mem_cons_of_mem _ member)))
        (fun value member => closed value (List.mem_cons_of_mem _ member)) head.2.1
      have initialLe : bound ≤ readAllGrowth (value :: values).length bound := readAllGrowth_ge _ _
      have ready := read_ready first bound (readAllGrowth (value :: values).length bound) semantic
        (available value List.mem_cons_self) (closed value List.mem_cons_self) fits initialLe
      refine ⟨head.1.trans tail.1, tail.2.1, ?_, .cons ready tail.2.2.2⟩
      have ownBound := Nat.le_trans head.2.2.1 (Nat.le_trans (readWidth_le_growth bound)
        (readAllGrowth_ge values.length (readGrowth bound)))
      have tailBound := tail.2.2.1
      simp only [List.length_append, List.length_cons, readAllGrowth, Nat.succ_mul]
      change own.length + more.length ≤
        values.length * readAllGrowth values.length (readGrowth bound) + readAllGrowth values.length (readGrowth bound)
      omega

/-- An initial operand count bounds every prefix and all literal concatenated rows. -/
theorem readAll {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)} (actual : SourceEqualityProjectionUnion.ReadAll values before rows after)
    (count bound : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (fits : Fits bound before)
    (length : values.length ≤ count) :
    Effect before after ∧ Fits (readAllGrowth count bound) after ∧
      rows.length ≤ count * readAllGrowth count bound ∧ Edges after rows ∧ ClosedEdges rows ∧
      SourceCurrentProjectionNumericReplay.ReadAllReady (readFuel (readAllGrowth count bound)) actual := by
  have checked := readAll_exact actual bound semantic costs available closed fits
  have grow := readAllGrowth_count_mono length bound
  have physical := actual.verified semantic available closed
  exact ⟨checked.1, SourceCurrentMemoMergeResourceControl.Fits.mono checked.2.1 grow,
    Nat.le_trans checked.2.2.1 (Nat.mul_le_mul length grow), physical.2.2.1, physical.2.2.2.1,
    checked.2.2.2.mono (readFuel_mono grow)⟩

/-- An actual closed source union pays all reads and its final literal node at the same return. -/
theorem union {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {result : Value Symbol Guard} (actual : SourceEqualityProjectionUnion.Union values before result after)
    (count bound : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (fits : Fits bound before)
    (length : values.length ≤ count) :
    Effect before after ∧ Fits (unionGrowth count bound) after ∧ Available after result ∧ result.free = [] ∧
      SourceCurrentProjectionNumericReplay.UnionReady (readFuel (unionGrowth count bound)) actual := by
  cases actual with
  | node reads built =>
      have first := readAll reads count bound semantic costs available closed fits length
      have final := SourceEqualityRequiredCache.node _ _ first.1.semantic.ready first.2.2.2.1 first.2.2.2.2.1
      have finalEffect : Effect _ _ :=
        ⟨final.1, SourceEqualityRequiredSemanticCache.node _ _ first.1.semantic first.2.2.2.1 first.2.2.2.2.1,
          InternedFreshOrdinaryCostHeap.preserve _ _ first.1.costs (InternedShallowHeap.makeNode_noNewMu _ _)⟩
      have resources := SourceCurrentMemoMergeResourceControl.node _ _ (readAllGrowth count bound)
        (count * readAllGrowth count bound) first.2.1 first.2.2.2.1 first.2.2.1
      have enough : readAllGrowth count bound ≤ unionGrowth count bound :=
        SourceCurrentMemoMergeResourceControl.primitiveGrowth_ge _ _
      have ready := first.2.2.2.2.2.mono (readFuel_mono enough)
      have resultSame := congrArg Prod.fst built
      have stateSame := congrArg Prod.snd built
      dsimp only at resultSame stateSame
      subst result
      subst after
      exact ⟨first.1.trans finalEffect, resources.1, final.2.1, final.2.2.1, .node reads rfl ready⟩

end Actual
end MicroCFTA.SourceCurrentProjectionUnionResources
