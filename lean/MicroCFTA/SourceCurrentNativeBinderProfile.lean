import MicroCFTA.SourceCurrentStoredMuFinishProfile
import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.SourceCurrentNativeRequestWinner
import MicroCFTA.SourceCurrentPublicationHeapInduction

/-!
# Pure profiles of actual completed source binders

Actual execution supplies the two current probes and the final selected
stored payload. The payload can come from an earlier writer. Its profile
contract gives the complete finish formula through the current ordinary
probe. The final heap must still supply that contract for every stored Mu.
-/
namespace MicroCFTA.SourceCurrentNativeBinderProfile
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedFreshOrdinaryDepthHeap (usesLocal)
open InternedStoredSubstitution (leaves)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile profile Equivalent)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (Correct shadow)
open SourceCurrentStoredMuTrackedProfile (erase)

/-- A real completed binder reduces to its current ordinary probe under the selected payload contract. -/
theorem build_profile [DecidableEq (EdgeKey Symbol Guard)]
    (smart : Bool) (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : build (.binder smart expression) environment before = .done value after)
    (heap : SourceCurrentPublicationHeapInduction.Heap Correct after) (assignment : Reference → Profile) :
    ∃ depth afterDepth ordinary cut entry body marker,
      callback expression environment .depth before = .done depth afterDepth ∧
      callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      after.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      value = finish smart (.mu entry body depth ordinary) ∧
      Correct entry body depth ordinary ∧
      (∀ leaf ∈ leaves body, marker ∉ (match leaf with
        | .reference name => assignment name | _ => profile leaf).getD []) ∧
      Equivalent (denote value assignment)
        (if !smart || usesLocal depth ordinary then
          if (Value.mu entry body depth ordinary).free.isEmpty then none
          else erase marker (denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment))
        else denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment)) := by
  obtain ⟨depth,afterDepth,ordinary,cut,rawOrdinary,afterRawOrdinary,
      depthDone,ordinaryDone,requestDone,_depthContext,_cutContext,afterContext,
      _rawDone,_filterDone,_rawContext,_growth,_issued,depthAvailable,ordinaryAvailable⟩ :=
    SourceCurrentNativeBinderExecution.decompose smart expression environment before value after context actual
  obtain ⟨selected,present,finished⟩ := SourceCurrentNativeRequestWinner.winner smart depth ordinary
    (callback expression environment) cut value after requestDone
  obtain ⟨entry,body,rfl⟩ := InternedProfileHeap.stored_probes depth ordinary selected after
    afterContext.base.normal.facts depthAvailable ordinaryAvailable present
  have available := afterContext.base.normal.facts.cached.nodes _ _ present
  have correct := heap _ entry body depth ordinary present
  obtain ⟨marker,fresh,matched⟩ := SourceCurrentStoredMuFinishProfile.complete smart entry body depth ordinary
    assignment after afterContext.base.normal.facts.coherent available
    (afterContext.depth _ entry body depth ordinary present) correct
  exact ⟨depth,afterDepth,ordinary,cut,entry,body,marker,depthDone,ordinaryDone,present,finished,
    correct,fresh,by simpa only [finished] using matched⟩

end MicroCFTA.SourceCurrentNativeBinderProfile
