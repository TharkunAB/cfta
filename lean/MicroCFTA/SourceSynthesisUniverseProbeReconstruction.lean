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
open InternedStoredSubstitutionRebind
open InternedBinderProtocol (Reference)
open SourceSynthesisUniverseBody (descriptors)
open SourceSynthesisUniverseResidentRows (Rows)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- Available resident source rows reconstruct the exact resident probe with no cache effect. -/
theorem execute_probe (top : Guard) (catalog : List (String × Nat)) (name probe : Reference)
    (source target : Value String Guard) (heap : InternedConstructorTemplates.State String Guard)
    (facts : Facts heap) (sourceAvailable : Available heap source) (targetAvailable : Available heap target)
    (sourceRows : Rows top catalog name source heap) (targetRows : Rows top catalog probe target heap) :
    InternedFreshOrdinaryStoredSubstitution.execute source (replacement name (.reference probe)) heap =
      .done target heap := by
  obtain ⟨sourceEntry, sourceMarker, sourceArrow, sourceRest, sourceEq, sourceMarkerRead,
      sourceChildren, sourceKey, sourceAligned, sourceResident, sourceClosed, sourceMarkerAvailable,
      sourceTop, sourceKinds, _sourceLive, _sourceRetained, _sourceNonempty⟩ :=
    sourceRows.readback facts
  obtain ⟨targetEntry, targetMarker, targetArrow, targetRest, targetEq, targetMarkerRead,
      _targetChildren, targetKey, targetAligned, targetResident, _targetClosed, targetMarkerAvailable,
      _targetTop, _targetKinds, targetLive, _targetRetained, targetNonempty⟩ :=
    targetRows.readback facts
  have markerSame : targetMarker = sourceMarker :=
    SourceSynthesisUniverseMarkerUnique.marker_eq "(->)" top targetMarker sourceMarker heap facts
      targetMarkerAvailable sourceMarkerAvailable targetMarkerRead sourceMarkerRead
  subst targetMarker
  have replayed := SourceSynthesisUniverseProbeRowAlignment.raw_rows_replay top name probe sourceMarker
    sourceArrow targetArrow (descriptors catalog) sourceRest targetRest heap facts sourceClosed
    sourceChildren sourceKey targetKey sourceAligned targetAligned targetResident
  have sourceNodeAvailable : Available heap
      (.node sourceEntry (canonicalEdges (sourceArrow :: sourceRest)) 0 [name]) := by
    rw [← sourceEq]
    exact sourceAvailable
  have bodyDone := SourceSynthesisUniverseCanonicalRowReplay.execute_eq_work_of_raw top name sourceEntry
    (sourceArrow :: sourceRest) (targetArrow :: targetRest) sourceMarker
    (replacement name (.reference probe)) heap facts sourceNodeAvailable sourceClosed
    sourceResident targetResident sourceTop sourceKinds replayed
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
  rw [sourceEq, bodyDone]
  simp only [InternedNestedConstruction.work, targetDone]

end MicroCFTA.SourceSynthesisUniverseProbeReconstruction
