import MicroCFTA.SourceCurrentConstrainedCapRequiredResources
import MicroCFTA.SourceCurrentMemoMergeUniformNumeric
import MicroCFTA.SourcePruningEnumerationSharedIncomingReservation
import MicroCFTA.SourcePruningEnumerationGuardWidth
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Current captured payload bounds for eager reservations

One current heap supplies the height, row, arity and projected-trie ceilings.
These bounds remain facts about its immutable payloads after later effects.
They do not assert that later heap records use the original guard alphabet.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEagerCapturedBounds
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationSharedIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar

/-- A current captured heap bounds all its available values and ordinary rows. -/
theorem captured_payload_bounds
    (seed : Seed) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (linked : InternedEdgeResidency.Linked heap)
    (bounded : SourceCurrentConstrainedCapRequiredResources.HeapFits seed.2 heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) heap) :
    (∀ value, InternedProbeProvenance.Available heap value →
      MergedOrdinaryHeight.height value ≤ scalar seed.2) ∧
    (∀ entry rows depth free,
      InternedProbeProvenance.Available heap (.node entry rows depth free) →
      rows.length ≤ scalar seed.2 ∧
      ∀ edge ∈ rows, edge.children.length ≤ scalar seed.2 ∧
        ∀ tries residual,
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ SourcePruningEnumerationGuardWidth.width seed.1) := by
  constructor
  · intro value available
    have mass := InternedValueMassHeap.available heap bounded.stored value available
    exact Nat.le_trans (SourceCurrentMemoMergeUniformNumeric.height_le_mass value)
      (Nat.le_trans mass (SourceCurrentConstrainedCapTargetForecast.scalar_mass seed.2))
  · intro entry rows depth free available
    refine ⟨SourceCurrentConstrainedCapRequiredResources.node_width bounded available, ?_⟩
    intro edge selected
    have resident := InternedEdgeResidency.resident_edges heap linked
      (.node entry rows depth free) available.resident edge selected
    refine ⟨SourceCurrentConstrainedCapRequiredResources.edge_width bounded edge resident, ?_⟩
    intro tries residual projected
    exact SourcePruningEnumerationGuardWidth.project_le seed.1 edge.entry.key.constraint tries residual
      (known edge.entry.key edge resident) projected

end MicroCFTA.SourcePruningEnumerationSharedEagerCapturedBounds
