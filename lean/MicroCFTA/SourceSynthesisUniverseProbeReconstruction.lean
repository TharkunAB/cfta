import MicroCFTA.SourceSynthesisUniverseResidentRows
import MicroCFTA.SourceSynthesisUniverseMarkerUnique
import MicroCFTA.SourceSynthesisUniverseNodeReplay
import MicroCFTA.SourceSynthesisUniverseProbeRowAlignment
import MicroCFTA.SourceSynthesisUniverseCanonicalRowReplay

/-!
# Physical stored reconstruction of an actual universe probe

The two resident row packets retain the same source descriptors.
Their available closed markers have the same complete cache record.
Actual stored substitution replays the target edges and target node.
The proof preserves the current constructor cache exactly.
-/
namespace MicroCFTA.SourceSynthesisUniverseProbeReconstruction
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind
open InternedBinderProtocol (Reference)
open SourceSynthesisUniverseBody (descriptors RowReadback)
open SourceSynthesisUniverseResidentRows (Rows)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- Actual source rows retain their ordered target replay and the complete target node request. -/
theorem probe_targets (top : Guard) (catalog : List (String × Nat)) (name probe : Reference)
    (source target : Value String Guard) (heap : InternedConstructorTemplates.State String Guard)
    (facts : Facts heap) (sourceAvailable : Available heap source) (targetAvailable : Available heap target)
    (sourceRows : Rows top catalog name source heap) (targetRows : Rows top catalog probe target heap) :
    ∃ sourceEntry marker targets,
      source = .node sourceEntry (nodeEdges source) 0 [name] ∧
      RowReadback "(->)" top [] marker ∧ Available heap marker ∧ marker.free = [] ∧
      (∀ row ∈ nodeEdges source, row.entry.key.constraint = top) ∧
      (∀ row ∈ nodeEdges source, ∀ child ∈ row.children, child = marker ∨ child = .reference name) ∧
      All₂ (fun row targetRow =>
        run (makeEdge row.entry.key.symbol top
          (row.children.map (input (replacement name (.reference probe))))) heap =
            (targetRow, heap)) (nodeEdges source) targets ∧
      (∀ row ∈ targets, EdgeResident heap row) ∧ run (makeNode targets) heap = (target, heap) := by
  obtain ⟨sourceEntry, sourceMarker, sourceArrow, sourceRest, sourceEq, sourceMarkerRead,
      sourceChildren, sourceKey, sourceAligned, sourceResident, sourceClosed, _rawSourceMarkerAvailable,
      sourceTop, sourceKinds, _sourceLive, sourceRetained, _sourceNonempty⟩ :=
    sourceRows.readback facts
  obtain ⟨targetEntry, targetMarker, targetArrow, targetRest, targetEq, targetMarkerRead,
      _targetChildren, targetKey, targetAligned, targetResident, _targetClosed, targetMarkerAvailable,
      _targetTop, _targetKinds, targetLive, _targetRetained, targetNonempty⟩ :=
    targetRows.readback facts
  have sourceMarkerAvailable : Available heap sourceMarker := by
    apply sourceAvailable.children sourceMarker
    rw [sourceEq]
    change sourceMarker ∈ (canonicalEdges (sourceArrow :: sourceRest)).flatMap EdgeValue.children
    apply List.mem_flatMap.mpr
    refine ⟨sourceArrow, sourceRetained, ?_⟩
    rw [sourceChildren]
    exact List.mem_cons_self
  have markerSame : targetMarker = sourceMarker :=
    SourceSynthesisUniverseMarkerUnique.marker_eq "(->)" top targetMarker sourceMarker heap facts
      targetMarkerAvailable sourceMarkerAvailable targetMarkerRead sourceMarkerRead
  subst targetMarker
  have replayed := SourceSynthesisUniverseProbeRowAlignment.raw_rows_replay top name probe sourceMarker
    sourceArrow targetArrow (descriptors catalog) sourceRest targetRest heap facts sourceClosed
    sourceChildren sourceKey targetKey sourceAligned targetAligned targetResident
  obtain ⟨canonicalTargets, canonicalReplay, _members, canonicalResident, sameNode⟩ :=
    SourceSynthesisUniverseCanonicalRowReplay.canonical_replay top (replacement name (.reference probe))
      (sourceArrow :: sourceRest) (targetArrow :: targetRest) heap facts sourceResident targetResident replayed
  have targetSurvive : surviving (targetArrow :: targetRest) = targetArrow :: targetRest := by
    unfold surviving
    apply List.filter_eq_self.mpr
    intro row member
    change (!EqualityLeafProjectionPhysical.dead row) = true
    simp only [targetLive row member, Bool.not_false]
  have targetNodeAvailable : Available heap
      (.node targetEntry (canonicalEdges (surviving (targetArrow :: targetRest))) 0 [probe]) := by
    rw [targetSurvive, ← targetEq]
    exact targetAvailable
  have nodeReplay := SourceSynthesisUniverseNodeReplay.resident_node_replay
    (targetArrow :: targetRest) targetEntry 0 [probe] heap facts targetNodeAvailable
    (by simpa only [targetSurvive] using targetNonempty)
  have targetDone : run (makeNode (targetArrow :: targetRest)) heap = (target, heap) := by
    simpa only [targetSurvive, ← targetEq] using nodeReplay
  have sourceEdges : nodeEdges source = canonicalEdges (sourceArrow :: sourceRest) := by
    simp only [sourceEq, nodeEdges]
  refine ⟨sourceEntry, sourceMarker, canonicalTargets, ?_, sourceMarkerRead, sourceMarkerAvailable,
    sourceClosed, ?_, ?_, ?_, canonicalResident, ?_⟩
  · rw [sourceEdges]
    exact sourceEq
  · intro row member
    exact sourceTop row (canonicalEdges_member _ row (sourceEdges ▸ member))
  · intro row member
    exact sourceKinds row (canonicalEdges_member _ row (sourceEdges ▸ member))
  · rw [sourceEdges]
    exact canonicalReplay
  · rw [sameNode]
    exact targetDone

/-- Available resident source rows reconstruct the exact resident probe with no cache effect. -/
theorem execute_probe (top : Guard) (catalog : List (String × Nat)) (name probe : Reference)
    (source target : Value String Guard) (heap : InternedConstructorTemplates.State String Guard)
    (facts : Facts heap) (sourceAvailable : Available heap source) (targetAvailable : Available heap target)
    (sourceRows : Rows top catalog name source heap) (targetRows : Rows top catalog probe target heap) :
    InternedFreshOrdinaryStoredSubstitution.execute source (replacement name (.reference probe)) heap =
      .done target heap := by
  obtain ⟨entry, marker, targets, sourceEq, _markerRead, _markerAvailable, closed, tops, kinds,
      replayed, _targetResident, nodeReplay⟩ :=
    probe_targets top catalog name probe source target heap facts sourceAvailable targetAvailable sourceRows targetRows
  have sourceNodeAvailable : Available heap (.node entry (nodeEdges source) 0 [name]) := by
    rw [← sourceEq]
    exact sourceAvailable
  have done := SourceSynthesisUniverseStoredRows.execute_reference_eq_work top name entry (nodeEdges source)
    targets marker (replacement name (.reference probe)) heap facts sourceNodeAvailable closed tops kinds replayed
  rw [← sourceEq] at done
  rw [done]
  simp only [InternedNestedConstruction.work, nodeReplay]

end MicroCFTA.SourceSynthesisUniverseProbeReconstruction
