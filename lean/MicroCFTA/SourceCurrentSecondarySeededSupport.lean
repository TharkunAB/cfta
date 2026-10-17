import MicroCFTA.SourceCurrentSecondaryProjectionScoped
import MicroCFTA.SourceCurrentClassGateCompletion

/-!
# Initial selected support from the actual false secondary gate

The original false class supplies support at its exact returned heap.
Semantic readiness and the cost heap derive the weighted gate input.
The signed paths retain the original order and duplicate occurrences.
Proper paths do not require unrelated forest roots to be closed.
-/
namespace MicroCFTA.SourceCurrentSecondarySeededSupport
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentSecondaryTrace SourceCurrentSecondaryProjectionScoped
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

/-- Mapping proper natural paths to signed paths preserves every occurrence's properness. -/
theorem mapped_proper {paths : EqualityNormalize.Class}
    (proper : ∀ path ∈ paths, path ≠ []) :
    ∀ path ∈ paths.map (List.map Int.ofNat), path ≠ [] := by
  intro path member
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
  intro empty
  exact proper original included (List.map_eq_nil_iff.mp empty)

/-- Initial heap facts and the actual false class derive the complete final support anchor. -/
theorem class_support [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before after : State Symbol Guard}
    (actual : ClassTrace unconstrained values paths before false after)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (proper : ∀ path ∈ paths, path ≠ []) :
    SemanticReady after ∧ CostHeap after ∧ GateReady after ∧ Keeps before after ∧
      Values after values ∧ ClassTrace unconstrained values paths after false after ∧
      ∀ path ∈ paths.map (List.map Int.ofNat), PathSupport unconstrained after path values := by
  obtain ⟨finalSemantic, ready, kept, finalAvailable, replay, pathsFalse⟩ :=
    SourceCurrentSecondaryProjectionAnchor.class_anchor unconstrained actual semantic
      (SourceCurrentClassGateCompletion.gate_ready semantic costs) available
  refine ⟨finalSemantic, ready.2.2.2, ready, kept, finalAvailable, replay, ?_⟩
  intro path member
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
  exact path_support_of_false (pathsFalse original included) (proper original included) finalAvailable

end MicroCFTA.SourceCurrentSecondarySeededSupport
