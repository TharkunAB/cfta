import MicroCFTA.SourceCurrentRawCorridorPositiveProjection

/-!
# Positive values returned by actual raw-corridor projections

The empty path retains the literal value. A proper projection returns an
ordinary value. Its actual zero-fuel read uses the existing row observers.
-/
namespace MicroCFTA.SourceCurrentRawCorridorPositiveValue
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
open SourceCurrentRequiredRawCorridor (RawCorridor)
open SourceCurrentRequiredPositivePosition (PositiveAt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem union_ordinary {values : List Node} {before after : Heap} {result : Node}
    (actual : Union values before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values) :
    Ordinary result := by
  cases actual with
  | node reads built =>
    have effects := SourceEqualityProjectionCosts.readAll_effects reads semantic costs available
    simpa only [built] using SourceEqualityRequiredCache.node_ordinary _ _
      effects.2.1.ready.semantic.1.normal.facts effects.2.2.2

private theorem project_ordinary {path : List Int} {value result : Node} {before after : Heap}
    (actual : Project path value before result after) :
    SemanticReady before → CostHeap before → Available before value → path ≠ [] → Ordinary result := by
  induction actual using Project.rec
      (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | root => intro _ _ _ impossible; exact (impossible rfl).elim
  | empty => intro _ _ _ _; trivial
  | ordinary rows combined _ =>
    intro semantic costs available _
    have resident := resident_edges _ semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have effects := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
    exact union_ordinary combined effects.2.1 effects.2.2.1 effects.2.2.2
  | recursive _ head _ ih =>
    intro semantic costs available nonempty
    have effects := SourceEqualityProjectionCosts.head_effects head semantic costs available
    exact ih effects.2.1 effects.2.2.1 effects.2.2.2 nonempty
  | nil => trivial
  | missing => trivial
  | selected => trivial

/-- The same projected value retains its full positive path in the corridor input. -/
theorem project {path residual : List Nat} {value result : Node} {before after : Heap}
    (actual : Project (path.map Int.ofNat) value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards before) (corridor : RawCorridor (path.map Int.ofNat) value)
    (positive : PositiveAt result residual) : PositiveAt value (path ++ residual) := by
  cases path with
  | nil => cases actual; exact positive
  | cons index path =>
    have effects := SourceEqualityProjectionCosts.project_effects actual semantic costs available
    have finalGuards := SourceCurrentConstrainedCapProjectionGuard.node Plain actual semantic costs available guards
    have ordinary := project_ordinary actual semantic costs available (by simp)
    have read : Read result after (nodeEdges result) after := by
      cases result with
      | empty | node => exact .done 0 rfl
      | reference | union | mu => cases ordinary
    cases positive with
    | root position row selected nonplain =>
      simpa only [List.append_nil] using SourceCurrentRawCorridorPositiveProjection.root actual read position row selected
        semantic costs available guards effects.2.1 (pure_keeps after effects.2.1.ready) finalGuards corridor nonplain
    | child position childIndex row child selected chosen rest =>
      exact SourceCurrentRawCorridorPositiveProjection.child actual read position row selected childIndex child chosen rest
        semantic costs available guards effects.2.1 (pure_keeps after effects.2.1.ready) finalGuards corridor
    | member => cases ordinary

end MicroCFTA.SourceCurrentRawCorridorPositiveValue
