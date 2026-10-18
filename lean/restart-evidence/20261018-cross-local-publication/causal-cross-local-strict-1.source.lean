import MicroCFTA.SourceCurrentPublicationCrossLocalGenerators
import MicroCFTA.SourceCurrentStoredReconstructionPath
import MicroCFTA.SourceCurrentGeneratedGrowth
import MicroCFTA.SourceCurrentCausalGeneratedEmpty

/-!
# Selected Mu reconstruction with distinct related local replacements

An issued publication path recovers the exact selected writer. Its body
and ordinary probe can use distinct available local replacements with
mutual source membership. Actual warm calls give membership at that reader.
Initial data also constructs both calls and membership at a produced reader.
Neither result asserts guarded observation equality at the original reader.
-/
namespace MicroCFTA.SourceCurrentCausalCrossLocalMuGenerators
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open SourceCurrentStoredMuBinderChildLineage (bind bound_replacements)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentRetainedMuDirectedCase (Generated)
open SourceCurrentOpenPreorderSimulation (Mutual)

/-- Actual warm calls for the selected writer retain distinct related local replacements. -/
theorem selected [DecidableEq (EdgeKey Symbol Guard)]
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (reader : State Symbol Guard) (ready : Ready reader) (path : Path empty reader)
    (present : reader.nodeRecords key = some (.mu entry body depth ordinary))
    (environment : Environment Symbol Guard) (replacements : Replacements reader environment)
    (firstLocal secondLocal : Value Symbol Guard)
    (firstAvailable : Available reader firstLocal) (secondAvailable : Available reader secondLocal)
    (related : Mutual (Generated reader) firstLocal secondLocal)
    (left right : Value Symbol Guard)
    (bodyDone : execute body (bind (.interned entry.identity) firstLocal environment) reader = .done left reader)
    (ordinaryDone : execute ordinary (bind (.uninterned (ordinaryLevel depth)) secondLocal environment) reader = .done right reader) :
    Mutual (Generated reader) left right := by
  obtain ⟨event,_keySame,valueSame,_missing,_prefix,_depthPath,_ordinaryPath,_bodyPath,growth⟩ :=
    SourceCurrentNativeMuGrowthWriters.from_empty path.forget key entry body depth ordinary present
  have payload : Value.mu entry body depth ordinary = Value.mu event.entry event.body event.depth event.ordinary := valueSame
  obtain ⟨sameEntry,sameBody,sameDepth,sameOrdinary⟩ := Value.mu.inj payload
  have available := ready.semantic.1.normal.facts.cached.nodes key _ present
  have eventAvailable : Available reader event.candidate := valueSame ▸ available
  have first : execute event.body (bind (.interned event.entry.identity) firstLocal environment) reader = .done left reader := by
    rw [←sameBody,←sameEntry]
    exact bodyDone
  have second : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) secondLocal environment) reader = .done right reader := by
    rw [←sameOrdinary,←sameDepth]
    exact ordinaryDone
  exact SourceCurrentPublicationCrossLocalGenerators.publication event reader ready growth eventAvailable
    environment replacements firstLocal secondLocal firstAvailable secondAvailable related left right first second

/-- Initial causal data constructs both calls and their mutual generators at one final reader. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (reader : State Symbol Guard) (ready : Ready reader) (path : Path empty reader)
    (present : reader.nodeRecords key = some (.mu entry body depth ordinary))
    (environment : Environment Symbol Guard) (replacements : Replacements reader environment)
    (firstLocal secondLocal : Value Symbol Guard)
    (firstAvailable : Available reader firstLocal) (secondAvailable : Available reader secondLocal)
    (related : Mutual (Generated reader) firstLocal secondLocal) :
    ∃ left middle right final,
      execute body (bind (.interned entry.identity) firstLocal environment) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) secondLocal environment) middle = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (Path reader middle) ∧ Nonempty (Path middle final) ∧ Nonempty (Path empty final) ∧
      final.nodeRecords key = some (.mu entry body depth ordinary) ∧
      execute body (bind (.interned entry.identity) firstLocal environment) final = .done left final ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) secondLocal environment) final = .done right final ∧
      Mutual (Generated final) firstLocal secondLocal ∧ Mutual (Generated final) left right ∧
      (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  have payloadAvailable := ready.semantic.1.normal.facts.cached.nodes key _ present
  have bodyAvailable := payloadAvailable.children body (by simp [children])
  have ordinaryAvailable := payloadAvailable.children ordinary (by simp [children])
  obtain ⟨left,middle,bodyDone,first,leftAvailable,⟨firstPath⟩⟩ :=
    SourceCurrentStoredReconstructionPath.complete body
      (bind (.interned entry.identity) firstLocal environment) reader ready bodyAvailable
      (bound_replacements _ firstLocal environment reader firstAvailable replacements)
  have middleReplacements : Replacements middle environment :=
    fun name value found => first.available value (replacements name value found)
  obtain ⟨right,final,ordinaryDone,second,rightAvailable,⟨secondPath⟩⟩ :=
    SourceCurrentStoredReconstructionPath.complete ordinary
      (bind (.uninterned (ordinaryLevel depth)) secondLocal environment) middle first.ready
      (first.available ordinary ordinaryAvailable)
      (bound_replacements _ secondLocal environment middle (first.available secondLocal secondAvailable) middleReplacements)
  have kept := first.trans second
  have finalPath : Path empty final := .trans path (.trans firstPath secondPath)
  have finalPresent : final.nodeRecords key = some (.mu entry body depth ordinary) :=
    kept.growth.nodeRecords _ _ present
  have bodyWarm := InternedFreshOrdinaryStoredSubstitution.execute_replay body
    (bind (.interned entry.identity) firstLocal environment) reader final left middle
    ready.semantic.1.normal.facts.coherent.valid bodyDone second.growth
  have ordinaryWarm := InternedFreshOrdinaryStoredSubstitution.execute_replay ordinary
    (bind (.uninterned (ordinaryLevel depth)) secondLocal environment) middle final right final
    first.ready.semantic.1.normal.facts.coherent.valid ordinaryDone (grows_refl _)
  have finalRelated : Mutual (Generated final) firstLocal secondLocal :=
    ⟨SourceCurrentGeneratedGrowth.generated related.1 kept,SourceCurrentGeneratedGrowth.generated related.2 kept⟩
  have generated := selected key entry body depth ordinary final kept.ready finalPath finalPresent
    environment (fun name value found => kept.available value (replacements name value found))
    firstLocal secondLocal (kept.available firstLocal firstAvailable) (kept.available secondLocal secondAvailable)
    finalRelated left right bodyWarm ordinaryWarm
  exact ⟨left,middle,right,final,bodyDone,ordinaryDone,first,second,second.available left leftAvailable,rightAvailable,
    ⟨firstPath⟩,⟨secondPath⟩,⟨finalPath⟩,finalPresent,bodyWarm,ordinaryWarm,finalRelated,generated,
    SourceCurrentCausalGeneratedEmpty.generated final finalPath.forget.history generated.1⟩

end MicroCFTA.SourceCurrentCausalCrossLocalMuGenerators
