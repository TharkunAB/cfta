import MicroCFTA.SourceCurrentProjectionUnionResources
import MicroCFTA.SourceCurrentConjunctionRowsWorker

/-!
# Initial resources for literal conjunction operand exposures

The original operand count fixes the ordered read schedule. Each read
retains its returned heap before the next operand starts. One computed
reader ceiling covers that complete sequence and every larger read fuel.
-/
namespace MicroCFTA.SourceCurrentConjunctionExposureResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentProjectionUnionResources
  (readGrowth readGrowth_ge readWidth_le_growth readAllGrowth readAllGrowth_ge
    readAllGrowth_mono readAllGrowth_count_mono readFuel)
open SourceCurrentConjunctionCompletionReads (Exposures)
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Formula : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- The original operand count determines the complete scalar envelope. -/
def forecast (count resource : Nat) : Nat := readAllGrowth count resource

/-- More original operands and larger initial resources retain every prefix. -/
theorem forecast_mono {firstCount lastCount firstResource lastResource : Nat}
    (counts : firstCount ≤ lastCount) (resources : firstResource ≤ lastResource) :
    forecast firstCount firstResource ≤ forecast lastCount lastResource :=
  readAllGrowth_mono counts resources

/-- The complete exposure schedule retains its initial scalar. -/
theorem forecast_ge (count resource : Nat) : resource ≤ forecast count resource :=
  readAllGrowth_ge count resource

/-- One final reader ceiling covers each exact intermediate read. -/
theorem of_exposures {nodes : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (List (EdgeValue Symbol Guard))} (actual : Exposures nodes before rows after)
    (resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before nodes) (closed : ClosedValues nodes) (fits : Fits resource before) :
    Fits (forecast nodes.length resource) after ∧ rows.length = nodes.length ∧
      (∀ row ∈ rows, row.length ≤ forecast nodes.length resource) ∧
      (∀ operations fuel, readFuel (forecast nodes.length resource) ≤ fuel →
        SourceCurrentConjunctionRowsWorker.exposures fuel nodes ⟨before, operations⟩ =
          .done rows ⟨after, operations⟩) := by
  induction actual generalizing resource with
  | nil => exact ⟨fits, rfl, by simp, by intros; rfl⟩
  | @cons value before own middle values more after first rest ih =>
      have head := SourceCurrentProjectionUnionResources.read first resource semantic costs
        (available value List.mem_cons_self) (closed value List.mem_cons_self) fits
      have tail := ih (readGrowth resource) head.1.semantic head.1.costs
        (fun child member => head.1.keeps.available child (available child (List.mem_cons_of_mem _ member)))
        (fun child member => closed child (List.mem_cons_of_mem _ member)) head.2.1
      have initialLe : resource ≤ forecast (value :: values).length resource := forecast_ge _ _
      have firstReady := SourceCurrentProjectionUnionResources.read_ready first resource
        (forecast (value :: values).length resource) semantic (available value List.mem_cons_self)
        (closed value List.mem_cons_self) fits initialLe
      have headWidth : own.length ≤ forecast (value :: values).length resource :=
        Nat.le_trans head.2.2.1 (Nat.le_trans (readWidth_le_growth resource)
          (readAllGrowth_ge values.length (readGrowth resource)))
      refine ⟨tail.1, congrArg Nat.succ tail.2.1, ?_, ?_⟩
      · intro row member
        rcases List.mem_cons.mp member with rfl | member
        · exact headWidth
        · exact tail.2.2.1 row member
      · intro operations fuel enough
        have done := SourceCurrentProjectionNumericReplay.ReadReady.mono firstReady enough
        have later := tail.2.2.2 operations fuel enough
        simp only [SourceCurrentConjunctionRowsWorker.exposures, done, later,
          SourceCurrentConjunctionRowsWorker.Outcome.bind]

/-- A count fixed before the first read also covers a shorter original operand list. -/
theorem bounded {nodes : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (List (EdgeValue Symbol Guard))} (actual : Exposures nodes before rows after)
    (count resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before nodes) (closed : ClosedValues nodes) (fits : Fits resource before)
    (length : nodes.length ≤ count) :
    Fits (forecast count resource) after ∧ rows.length = nodes.length ∧
      (∀ row ∈ rows, row.length ≤ forecast count resource) ∧
      (∀ operations fuel, readFuel (forecast count resource) ≤ fuel →
        SourceCurrentConjunctionRowsWorker.exposures fuel nodes ⟨before, operations⟩ =
          .done rows ⟨after, operations⟩) := by
  have own := of_exposures actual resource semantic costs available closed fits
  have larger := forecast_mono length (Nat.le_refl resource)
  exact ⟨own.1.mono larger, own.2.1,
    fun row member => Nat.le_trans (own.2.2.1 row member) larger,
    fun operations fuel enough => own.2.2.2 operations fuel
      (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono larger) enough)⟩

/-- Initial closed resident operands construct their own complete exposure and numeric receipt. -/
theorem complete (nodes : List (Value Symbol Guard))
    (before : SourceCurrentConjunctionRowsAllocation.State Symbol Formula)
    (count resource : Nat) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (fits : Fits resource before.heap) (length : nodes.length ≤ count) :
    ∃ rows heap, Exposures nodes before.heap rows heap ∧
      SourceCurrentConjunctionRowsAllocation.Ready ⟨heap, before.equality⟩ ∧
      SourceCurrentConjunctionRowsAllocation.Effects before ⟨heap, before.equality⟩ ∧
      Fits (forecast count resource) heap ∧ rows.length = nodes.length ∧
      (∀ row ∈ rows, row.length ≤ forecast count resource ∧ Edges heap row ∧ ClosedEdges row) ∧
      (∀ fuel, readFuel (forecast count resource) ≤ fuel →
        SourceCurrentConjunctionRowsWorker.exposures fuel nodes before = .done rows ⟨heap, before.equality⟩) := by
  obtain ⟨rows, heap, actual, effects, resident⟩ :=
    SourceCurrentConjunctionCompletionReads.exposures_complete
      (SourceCurrentConjunctionEquality.FieldAvailable before.equality) nodes before.heap
      ready.semantic ready.costs ready.fields available closed
  have numeric := bounded actual count resource ready.semantic ready.costs available closed fits length
  have finalReady : SourceCurrentConjunctionRowsAllocation.Ready ⟨heap, before.equality⟩ :=
    ⟨effects.semantic, effects.costs, ready.valid, effects.annotations⟩
  exact ⟨rows, heap, actual, finalReady,
    ⟨effects.keeps, finalReady, SourceEqualityConstraintMemoAllocation.grows_refl _⟩,
    numeric.1, numeric.2.1,
    fun row member => ⟨numeric.2.2.1 row member, resident row member⟩,
    fun fuel enough => numeric.2.2.2 before.equality fuel enough⟩

end MicroCFTA.SourceCurrentConjunctionExposureResources
