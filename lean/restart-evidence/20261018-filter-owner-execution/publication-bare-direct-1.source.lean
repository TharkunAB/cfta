import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.InternedActualProbeTags

/-!
# Actual repaired publications agree on the bare-self branch

The Depth callback selects the repaired fresh ordinary level. Its actual
profile excludes that level from the fixed root captures. Reservation
excludes the fresh interned name from all earlier captures. Both filtered
callbacks therefore have bare-self shape at the same source case.
-/
namespace MicroCFTA.SourceCurrentPublicationBareParity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext (Context)
open InternedNestedProvenance (Values)
open InternedRootProfile InternedProfileCallbackForm InternedProfileEquivalence
open InternedProfileSemantics (evaluate)
open InternedTwoProbeProfiles
open InternedBinderProtocol (Reference)
open SourceCurrentNativeMuPublication (Publication)

private theorem callback_profile [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (name : Reference) (before after : State Symbol Guard) (context : Context before environment)
    (argument : Available before (.reference name)) (value : Value Symbol Guard)
    (actual : callback expression environment name before = .done value after) :
    Equivalent (profile value) (normalize name (evaluate expression (some [name] :: environment.map profile))) := by
  have localContext := context.local name argument
  have checked := InternedFreshOrdinaryProfileExecutionFacts.callback_checked expression environment name before
    context.normal localContext.inputs (by
      simpa only [List.map_cons,profile] using
        InternedFreshOrdinaryProfiles.build_profile expression (.reference name :: environment) before
          context.normal localContext.inputs context.profiles)
  exact checked.result value after actual

/-- Actual filtered body and ordinary callbacks enter the bare-self case together. -/
theorem bare [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    event.body = .reference (.interned event.entry.identity) ↔
      event.ordinary = .reference (.uninterned (ordinaryLevel event.depth)) := by
  obtain ⟨depthContext,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  let own : Reference := .interned event.entry.identity
  let ordinary : Reference := .uninterned (ordinaryLevel event.depth)
  have depthArgument : Available event.before (.reference .depth) := InternedNestedProvenance.depth_available event.before
  have ordinaryArgument : Available event.afterDepth (.reference ordinary) :=
    InternedNestedProvenance.ordinary_available event.afterDepth (ordinaryLevel event.depth)
  have bodyArgument : Available event.allocated (.reference own) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have depthProfile := callback_profile event.expression event.environment .depth event.before event.afterDepth
    event.context.base depthArgument event.depth event.depthDone
  have ordinaryProfile := callback_profile event.expression event.environment ordinary event.afterDepth event.cut
    depthContext.base ordinaryArgument event.ordinary event.ordinaryDone
  have bodyProfile := callback_profile event.expression event.environment own event.allocated event.afterBody
    bodyContext.base bodyArgument event.body event.bodyDone
  have depthAvailable := (callback_verified event.expression event.environment .depth event.before
    event.context.base.normal.facts (event.context.base.local .depth depthArgument).inputs).result
      event.depth event.afterDepth event.depthDone
  have ordinaryAvailable := (callback_verified event.expression event.environment ordinary event.afterDepth
    depthContext.base.normal.facts (depthContext.base.local ordinary ordinaryArgument).inputs).result
      event.ordinary event.cut event.ordinaryDone
  have bodyAvailable := (callback_verified event.expression event.environment own event.allocated
    bodyContext.base.normal.facts (bodyContext.base.local own bodyArgument).inputs).result
      event.body event.afterBody event.bodyDone
  have bodyNormal : InternedStoredMuOrigins.Normal event.afterBody := by
    simpa only [event.bodyDone,Outcome.state] using
      (bodyContext.callback event.expression own bodyArgument).base.normal
  cases computed : symbolic event.expression (event.environment.map profile) with
  | none =>
      have bodyHidden : profile event.body = none := bodyProfile.1.mpr (by
        rw [opaque_form event.expression (event.environment.map profile) computed]; rfl)
      have ordinaryHidden : profile event.ordinary = none := ordinaryProfile.1.mpr (by
        rw [opaque_form event.expression (event.environment.map profile) computed]; rfl)
      exact iff_of_false (InternedActualProbeTags.opaque_tags event.body own bodyHidden).2
        (InternedActualProbeTags.opaque_tags event.ordinary ordinary ordinaryHidden).2
  | some names =>
      let captured := captures names
      let uses := usesArgument names
      have form (name : Reference) := normalize_same name
        (pure_form event.expression (event.environment.map profile) names computed name)
      have depthForm := trans depthProfile (form .depth)
      have ordinaryForm := trans ordinaryProfile (form ordinary)
      have bodyForm := trans bodyProfile (form own)
      have ordinaryFresh : ordinary ∉ captured := by
        intro present
        have rawMember : ordinary ∈ response captured uses .depth :=
          (response_member captured uses .depth ordinary).mpr (Or.inl present)
        have normalized : ordinary ∈ (probe captured uses .depth).getD [] :=
          (normalize_other .depth ordinary (by intro impossible; cases impossible) _).mpr rawMember
        have actual := (depthForm.2 ordinary).mpr normalized
        exact ordinary_fresh event.depth
          (InternedProfileFree.member_free event.depth ordinary event.afterDepth
            depthContext.base.normal.facts.coherent depthAvailable actual)
      have ownFresh : own ∉ captured := by
        apply InternedProfileOrigins.captures_fresh event.expression (event.environment.map profile) names computed own
        intro input member present
        obtain ⟨value,included,rfl⟩ := List.mem_map.mp member
        have available := cutContext.base.inputs value included
        have free := InternedProfileFree.member_free value own event.cut cutContext.base.normal.facts.coherent available present
        have fresh := InternedFreshProbeKeys.next_absent event.cut.nodes cutContext.base.normal.facts.coherent.valid.2
          value available.issued
        have selected : own = .interned event.cut.nodes.next := congrArg Reference.interned
          (InternedFreshProbeKeys.intern_miss_identity event.cut.nodes event.key event.missing)
        exact fresh (selected ▸ free)
      have bodySelf := InternedActualProbeTags.self_form event.body event.afterBody bodyNormal
        bodyAvailable captured uses own bodyForm
      have ordinarySelf := InternedActualProbeTags.self_form event.ordinary event.cut cutContext.base.normal
        ordinaryAvailable captured uses ordinary ordinaryForm
      rw [probe,normalize_single,response_single captured uses own ownFresh] at bodySelf
      rw [probe,normalize_single,response_single captured uses ordinary ordinaryFresh] at ordinarySelf
      exact bodySelf.trans ordinarySelf.symm

end MicroCFTA.SourceCurrentPublicationBareParity
