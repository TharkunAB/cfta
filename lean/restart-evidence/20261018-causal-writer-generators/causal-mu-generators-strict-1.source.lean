import MicroCFTA.SourceCurrentPublicationReconstructionGenerators
import MicroCFTA.SourceCurrentStoredReconstructionPath
import MicroCFTA.SourceCurrentCausalStoredMuReadback

/-!
# Actual selected Mu reconstruction generators

An actual issued publication path recovers the selected writer. Its body
and ordinary probe retain both source generators under arbitrary common
outer and local replacements. Initial ready data constructs both calls
and their complete issued paths. Replay places both generators at one
produced reader. This does not prove their guarded observation clauses.
-/
namespace MicroCFTA.SourceCurrentCausalStoredMuGenerators
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentRetainedMuDirectedCase (Generated)
open InternedNestedConstruction (Outcome)
open InternedRootProfile (Equivalent profile)

private theorem bound_replacements (name : Reference) (replacement : Value Symbol Guard)
    (environment : Environment Symbol Guard) (reader : State Symbol Guard)
    (available : Available reader replacement) (replacements : Replacements reader environment) :
    Replacements reader (bind name replacement environment) := by
  intro queried value found
  dsimp only [SourceCurrentStoredMuBinderChildLineage.bind] at found
  split at found
  · cases found; exact available
  · exact replacements queried value found

/-- An actual selected record and its same-reader calls derive both historical source generators. -/
theorem selected [DecidableEq (EdgeKey Symbol Guard)]
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (reader : State Symbol Guard) (ready : Ready reader) (path : Path empty reader)
    (present : reader.nodeRecords key = some (.mu entry body depth ordinary))
    (environment : Environment Symbol Guard) (replacements : Replacements reader environment)
    (replacement : Value Symbol Guard) (localAvailable : Available reader replacement)
    (left right : Value Symbol Guard)
    (bodyDone : execute body (bind (.interned entry.identity) replacement environment) reader = .done left reader)
    (ordinaryDone : execute ordinary (bind (.uninterned (ordinaryLevel depth)) replacement environment) reader = .done right reader) :
    Generated reader left right ∧ Generated reader right left := by
  obtain ⟨event,_keySame,valueSame,_missing,_prefix,_depthPath,_ordinaryPath,_bodyPath,growth⟩ :=
    SourceCurrentNativeMuGrowthWriters.from_empty path.forget key entry body depth ordinary present
  have payload : Value.mu entry body depth ordinary = Value.mu event.entry event.body event.depth event.ordinary := valueSame
  obtain ⟨sameEntry,sameBody,sameDepth,sameOrdinary⟩ := Value.mu.inj payload
  have available := ready.semantic.1.normal.facts.cached.nodes key _ present
  have eventAvailable : Available reader event.candidate := valueSame ▸ available
  have first : execute event.body (bind (.interned event.entry.identity) replacement environment) reader = .done left reader := by
    rw [←sameBody,←sameEntry]
    exact bodyDone
  have second : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) replacement environment) reader = .done right reader := by
    rw [←sameOrdinary,←sameDepth]
    exact ordinaryDone
  exact SourceCurrentPublicationReconstructionGenerators.publication event reader ready growth eventAvailable
    environment replacements replacement localAvailable left right first second

/-- Initial causal data constructs both exact calls, issued paths and warm generators at one final reader. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (reader : State Symbol Guard) (ready : Ready reader) (path : Path empty reader)
    (present : reader.nodeRecords key = some (.mu entry body depth ordinary))
    (environment : Environment Symbol Guard) (replacements : Replacements reader environment)
    (replacement : Value Symbol Guard) (localAvailable : Available reader replacement) :
    ∃ left middle right final,
      execute body (bind (.interned entry.identity) replacement environment) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) replacement environment) middle = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (Path reader middle) ∧ Nonempty (Path middle final) ∧ Nonempty (Path empty final) ∧
      final.nodeRecords key = some (.mu entry body depth ordinary) ∧
      execute body (bind (.interned entry.identity) replacement environment) final = .done left final ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) replacement environment) final = .done right final ∧
      Generated final left right ∧ Generated final right left ∧
      Equivalent (profile left) (profile right) ∧
      (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  obtain ⟨left,middle,right,final,firstDone,secondDone,first,second,leftAvailable,rightAvailable,
    _firstHistory,_secondHistory,_middlePresent,finalPresent,profiles,emptyFlags⟩ :=
    SourceCurrentCausalStoredMuReadback.complete key entry body depth ordinary reader ready path.forget.history
      present environment replacements replacement localAvailable
  have payloadAvailable := ready.semantic.1.normal.facts.cached.nodes key _ present
  have bodyAvailable := payloadAvailable.children body (by simp [children])
  have ordinaryAvailable := payloadAvailable.children ordinary (by simp [children])
  obtain ⟨firstPath⟩ := SourceCurrentStoredReconstructionPath.actual body
    (bind (.interned entry.identity) replacement environment) reader ready bodyAvailable
    (bound_replacements _ replacement environment reader localAvailable replacements) left middle firstDone
  have middleReplacements : Replacements middle environment :=
    fun name value found => first.available value (replacements name value found)
  obtain ⟨secondPath⟩ := SourceCurrentStoredReconstructionPath.actual ordinary
    (bind (.uninterned (ordinaryLevel depth)) replacement environment) middle first.ready
    (first.available ordinary ordinaryAvailable)
    (bound_replacements _ replacement environment middle (first.available replacement localAvailable) middleReplacements)
    right final secondDone
  have finalPath : Path empty final := .trans path (.trans firstPath secondPath)
  have kept := first.trans second
  have bodyWarm := InternedFreshOrdinaryStoredSubstitution.execute_replay body
    (bind (.interned entry.identity) replacement environment) reader final left middle
    ready.semantic.1.normal.facts.coherent.valid firstDone second.growth
  have ordinaryWarm := InternedFreshOrdinaryStoredSubstitution.execute_replay ordinary
    (bind (.uninterned (ordinaryLevel depth)) replacement environment) middle final right final
    first.ready.semantic.1.normal.facts.coherent.valid secondDone (grows_refl _)
  have generated := selected key entry body depth ordinary final kept.ready finalPath finalPresent
    environment (fun name value found => kept.available value (replacements name value found))
    replacement (kept.available replacement localAvailable) left right bodyWarm ordinaryWarm
  exact ⟨left,middle,right,final,firstDone,secondDone,first,second,leftAvailable,rightAvailable,
    ⟨firstPath⟩,⟨secondPath⟩,⟨finalPath⟩,finalPresent,bodyWarm,ordinaryWarm,generated.1,generated.2,profiles,emptyFlags⟩

/-- Actual selected Mu unfolding supplies both epsilon endpoints and the generated ordinary-probe comparison. -/
theorem unfolding [DecidableEq (EdgeKey Symbol Guard)]
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (reader : State Symbol Guard) (ready : Ready reader) (path : Path empty reader)
    (present : reader.nodeRecords key = some (.mu entry body depth ordinary)) :
    ∃ left middle right final,
      unfold (.mu entry body depth ordinary) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) (.mu entry body depth ordinary) (fun _ => none))
        middle = .done right final ∧
      unfold (.mu entry body depth ordinary) final = .done left final ∧
      left ∈ MergedFreshOrdinaryGraph.successors reader (.mu entry body depth ordinary) ∧
      left ∈ MergedFreshOrdinaryGraph.successors final (.mu entry body depth ordinary) ∧
      Keeps reader middle ∧ Keeps middle final ∧ Nonempty (Path empty final) ∧
      Generated final left right ∧ Generated final right left := by
  have available := ready.semantic.1.normal.facts.cached.nodes key _ present
  obtain ⟨left,middle,right,final,firstDone,secondDone,first,second,_leftAvailable,_rightAvailable,
    _firstPath,_secondPath,finalPath,_finalPresent,bodyWarm,_ordinaryWarm,forward,backward,_profiles,_emptyFlags⟩ :=
    complete key entry body depth ordinary reader ready path present (fun _ => none)
      (by intro name value impossible; cases impossible) (.mu entry body depth ordinary) available
  have firstUnfold : unfold (.mu entry body depth ordinary) reader = .done left middle := firstDone
  have finalUnfold : unfold (.mu entry body depth ordinary) final = .done left final := bodyWarm
  have initialEpsilon : left ∈ MergedFreshOrdinaryGraph.successors reader (.mu entry body depth ordinary) := by
    simp only [MergedFreshOrdinaryGraph.successors,firstUnfold,List.mem_singleton]
  have finalEpsilon : left ∈ MergedFreshOrdinaryGraph.successors final (.mu entry body depth ordinary) := by
    simp only [MergedFreshOrdinaryGraph.successors,finalUnfold,List.mem_singleton]
  exact ⟨left,middle,right,final,firstUnfold,secondDone,finalUnfold,initialEpsilon,finalEpsilon,
    first,second,finalPath,forward,backward⟩

end MicroCFTA.SourceCurrentCausalStoredMuGenerators
