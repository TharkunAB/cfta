import MicroCFTA.SourcePruningOuterNarrow
import MicroCFTA.SourceCurrentConstrainedCapRequiredResources
import MicroCFTA.SourceEqualityAnnotationExposure

/-!
# Initial resources at the actual narrowing endpoint

The row reader retains its actual returned heap. The filter retains original
rows. One node constructor bounds the final heap. The guard alphabet does
not change. These observers do not assert completion at an arbitrary fuel.
-/
namespace MicroCFTA.SourcePruningNativeView
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapRequiredResources (HeapFits)
open SourceCurrentConstrainedCapEditForecast (scalar headProfile)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Key : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial resources bound the same successful filtered-node endpoint. -/
theorem narrowAt_resources
    (profile : Profile) (alphabet : Guard → Prop)
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool) (key : Key)
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : narrowAt fits admits fuel key value before = .done result after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before value) (closed : value.free = [])
    (bounded : HeapFits profile before) (known : SourceEqualityAnnotationHeap.Heap alphabet before) :
    HeapFits (headProfile profile) after ∧ SourceEqualityAnnotationHeap.Heap alphabet after := by
  unfold narrowAt at actual
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | unresolved | pending | exhausted => simp only [exposed] at actual; cases actual
  | done rows middle =>
      have built : run (makeNode (rows.filter (keeps fits admits key))) middle = (result, after) := by
        exact Prod.ext (MergedSourceComparison.Result.done.inj (by simpa only [exposed] using actual)).1
          (MergedSourceComparison.Result.done.inj (by simpa only [exposed] using actual)).2
      have read := SourceCurrentProjectionUnionResources.read (.done fuel exposed)
        (scalar profile) semantic costs available closed bounded.scalar_fits
      have selected : InternedNestedProvenance.Edges middle (rows.filter (keeps fits admits key)) :=
        fun row member => read.2.2.2.1 row (List.mem_filter.mp member).1
      have length : (rows.filter (keeps fits admits key)).length ≤
          SourceCurrentProjectionUnionResources.readWidth (scalar profile) :=
        Nat.le_trans (List.length_filter_le _ _) read.2.2.1
      have constructed := SourceCurrentMemoMergeResourceControl.node
        (rows.filter (keeps fits admits key)) middle
        (SourceCurrentProjectionUnionResources.readGrowth (scalar profile))
        (SourceCurrentProjectionUnionResources.readWidth (scalar profile)) read.2.1 selected length
      have middleKnown : SourceEqualityAnnotationHeap.Heap alphabet middle := by
        have retained := SourceEqualityAnnotationExposure.nodeEdges_heap alphabet fuel value before
          semantic.ready.semantic semantic.ready.covered known available closed
        simpa only [exposed, MergedSourceExposure.Result.state] using retained
      have finalKnown := SourceEqualityAnnotationHeap.run alphabet
        (makeNode (rows.filter (keeps fits admits key)))
        (SourceEqualityAnnotationHeap.makeNode alphabet _) middle middleKnown
      rw [built] at constructed finalKnown
      exact ⟨⟨constructed.1.nodes, constructed.1.edges, constructed.1.stored⟩, finalKnown⟩

end MicroCFTA.SourcePruningNativeView

namespace MicroCFTA.SourcePruningOuterNarrow
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapRequiredResources (HeapFits)
open SourceCurrentConstrainedCapEditForecast (headProfile headProfile_ge)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Typing Key : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Mu and type skips or the actual filter retain the original resource forecast. -/
theorem narrow_resources
    (profile : Profile) (alphabet : Guard → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel uv : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : narrow holeKey fits admits metadata fuel uv value before = .done result after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before value) (closed : value.free = [])
    (bounded : HeapFits profile before) (known : SourceEqualityAnnotationHeap.Heap alphabet before) :
    HeapFits (headProfile profile) after ∧ SourceEqualityAnnotationHeap.Heap alphabet after := by
  have skipped (same : result = value ∧ after = before) :
      HeapFits (headProfile profile) after ∧ SourceEqualityAnnotationHeap.Heap alphabet after := by
    rcases same with ⟨rfl, rfl⟩
    exact ⟨bounded.mono (headProfile_ge profile), known⟩
  by_cases typed : uv ∈ metadata.types
  · have pureDone := narrow_type holeKey fits admits metadata fuel uv value before typed
    have parts := MergedSourceComparison.Result.done.inj (pureDone.symm.trans actual)
    exact skipped ⟨parts.1.symm, parts.2.symm⟩
  · cases value with
    | mu =>
        have parts := MergedSourceComparison.Result.done.inj actual
        exact skipped ⟨parts.1.symm, parts.2.symm⟩
    | empty | reference | node | union =>
        have narrowed := actual
        simp [narrow, typed] at narrowed
        exact SourcePruningNativeView.narrowAt_resources profile alphabet fits admits
          (holeKey metadata.typing uv) fuel _ before result after narrowed semantic costs
          available closed bounded known

end MicroCFTA.SourcePruningOuterNarrow
