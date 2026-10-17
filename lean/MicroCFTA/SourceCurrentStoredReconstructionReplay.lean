import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.InternedFreshOrdinaryReplay

/-!
# Common final replay of stored Mu reconstruction

An initial source publication history extends through both actual calls.
Both completed calls replay at their common final heap. The original Mu
retains its actual writer. The theorem does not compare the two results.
-/
namespace MicroCFTA.SourceCurrentStoredReconstructionReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (leaves input encode)
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (History Written)

/-- An initial publication history supplies both final replays and the retained original writer. -/
theorem mu [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary replacement : Value Symbol Guard) (before : State Symbol Guard)
    (ready : Ready before) (present : before.nodeRecords key = some (.mu entry body depth ordinary))
    (replacementAvailable : Available before replacement) (history : History empty before) :
    ∃ left middle right after,
      InternedFreshOrdinaryStoredSubstitution.execute body
        (fun name => if name = .interned entry.identity then some replacement else none) before = .done left middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary
        (fun name => if name = .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)
          then some replacement else none) middle = .done right after ∧
      Keeps before middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      Nonempty (History before middle) ∧ Nonempty (History middle after) ∧ Nonempty (History empty after) ∧
      after.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Written empty key (.mu entry body depth ordinary) ∧
      InternedFreshOrdinaryStoredSubstitution.execute body
        (fun name => if name = .interned entry.identity then some replacement else none) after = .done left after ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary
        (fun name => if name = .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)
          then some replacement else none) after = .done right after := by
  obtain ⟨left, middle, right, after, bodyDone, ordinaryDone, first, second, leftAvailable, rightAvailable,
      firstHistory, secondHistory, retained⟩ :=
    SourceCurrentStoredReconstruction.mu key entry body depth ordinary replacement before ready present replacementAvailable
  obtain ⟨firstEvents⟩ := firstHistory
  obtain ⟨secondEvents⟩ := secondHistory
  have whole : History empty after := .trans history (.trans firstEvents secondEvents)
  refine ⟨left, middle, right, after, bodyDone, ordinaryDone, first, second, leftAvailable, rightAvailable,
    ⟨firstEvents⟩, ⟨secondEvents⟩, ⟨whole⟩, retained, whole.from_empty key entry body depth ordinary retained, ?_, ?_⟩
  · exact InternedFreshOrdinaryReplay.build_replay (encode (leaves body) [] body) _ before after left middle
      ready.semantic.1.normal.facts.coherent.valid bodyDone second.growth
  · exact InternedFreshOrdinaryReplay.build_replay (encode (leaves ordinary) [] ordinary) _ middle after right after
      first.ready.semantic.1.normal.facts.coherent.valid ordinaryDone (grows_refl after)

end MicroCFTA.SourceCurrentStoredReconstructionReplay
