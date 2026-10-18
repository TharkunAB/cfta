import MicroCFTA.SourceCurrentStoredMuFinishProfile
import MicroCFTA.SourceCurrentPublicationHeapInduction
import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.SourceCurrentNativeRequestWinner
import MicroCFTA.SourceCurrentStoredRootDeletion

/-!
# Actual retained Mu profiles at a common later contract heap

The actual selected payload retains its complete current probes. Forward
record growth obtains its profile contract at the reader. A fresh marker
reduces its retained open result to the actual ordinary probe. The source
publication step of the reader's contract heap remains a separate proof.
-/
namespace MicroCFTA.SourceCurrentNativeRetainedRootDeletion
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax finish)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile profile Equivalent)
open InternedStoredSubstitution (leaves)
open InternedFreshOrdinaryDepthHeap (usesLocal)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentPublicationHeapInduction (Heap)
open SourceCurrentStoredMuProfileContract (Correct shadow)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuTrackedProfile (erase)
open SourceCurrentStoredRootDeletion (deleted)

/-- Two finite assigned body-leaf collections admit one common literal marker. -/
theorem fresh_pair (first second : Value Symbol Guard)
    (firstAssignment secondAssignment : Reference → Profile) :
    ∃ marker : Reference,
      (∀ leaf ∈ leaves first, marker ∉ (match leaf with
        | .reference name => firstAssignment name | _ => profile leaf).getD []) ∧
      (∀ leaf ∈ leaves second, marker ∉ (match leaf with
        | .reference name => secondAssignment name | _ => profile leaf).getD []) := by
  obtain ⟨marker,fresh⟩ := SourceCurrentStoredMuProfileReduction.fresh_marker
    (((leaves first).map (fun leaf => match leaf with
      | .reference name => firstAssignment name | _ => profile leaf)) ++
     ((leaves second).map (fun leaf => match leaf with
      | .reference name => secondAssignment name | _ => profile leaf)))
  refine ⟨marker,?_,?_⟩
  · intro leaf member
    exact fresh _ (List.mem_append_left _ (List.mem_map.mpr ⟨leaf,member,rfl⟩))
  · intro leaf member
    exact fresh _ (List.mem_append_right _ (List.mem_map.mpr ⟨leaf,member,rfl⟩))

/-- Actual retained readback reduces through its selected contract and the current strict-body schedule. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)]
    (smart : Bool) (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build (.binder smart expression) environment before = .done value after)
    (reader : State Symbol Guard) (later : Grows after reader) (heap : Heap Correct reader) :
    ∃ depth afterDepth ordinary cut raw afterRaw entry body,
      callback expression environment .depth before = .done depth afterDepth ∧
      callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      InternedFreshOrdinaryConstruction.build expression
        (.reference (.uninterned (ordinaryLevel depth)) :: environment) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (ordinary,cut) ∧
      Grows afterRaw after ∧ Extends afterRaw.nodes.issued after.nodes.issued ∧
      after.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      reader.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      Correct entry body depth ordinary ∧ value = finish smart (.mu entry body depth ordinary) ∧
      ((!smart || usesLocal depth ordinary) = true →
        value = .mu entry body depth ordinary ∧
        ∀ (cuts : Reference → Bool) (assignment : Reference → Profile) (marker : Reference),
          (∀ leaf ∈ leaves body, marker ∉ (match leaf with
            | .reference name => assignment name | _ => profile leaf).getD []) →
          Equivalent (deleted cuts value assignment)
            (if (Value.mu entry body depth ordinary).free.isEmpty then none
              else erase marker (denote ordinary
                (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment)))) := by
  obtain ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,
      depthDone,ordinaryDone,requestDone,_depthContext,_cutContext,afterContext,
      rawDone,filterDone,_rawContext,growth,issued,depthAvailable,ordinaryAvailable⟩ :=
    SourceCurrentNativeBinderExecution.decompose smart expression environment before value after context actual
  obtain ⟨selected,present,finished⟩ := SourceCurrentNativeRequestWinner.winner smart depth ordinary
    (callback expression environment) cut value after requestDone
  obtain ⟨entry,body,rfl⟩ := InternedProfileHeap.stored_probes depth ordinary selected after
    afterContext.base.normal.facts depthAvailable ordinaryAvailable present
  have atReader := later.nodeRecords _ _ present
  have correct := heap _ entry body depth ordinary atReader
  have available := afterContext.base.normal.facts.cached.nodes _ _ present
  have decoded := afterContext.depth _ entry body depth ordinary present
  refine ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,entry,body,
    depthDone,ordinaryDone,rawDone,filterDone,growth,issued,present,atReader,correct,finished,?_⟩
  intro keep
  have retained : finish smart (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
    cases smart with
    | false => rfl
    | true =>
        have used : usesLocal depth ordinary = true := by simpa only [Bool.not_true,Bool.false_or] using keep
        exact SourceCurrentNativeNormalizedComparison.retained_of_used entry body depth ordinary decoded used
  refine ⟨finished.trans retained,?_⟩
  intro cuts assignment marker fresh
  have reduced := SourceCurrentStoredMuFinishProfile.finish_profile smart entry body depth ordinary assignment after
    afterContext.base.normal.facts.coherent available decoded correct marker fresh
  simp only [keep,ite_true] at reduced
  rw [retained] at reduced
  rw [finished,retained,deleted]
  exact reduced

end MicroCFTA.SourceCurrentNativeRetainedRootDeletion
