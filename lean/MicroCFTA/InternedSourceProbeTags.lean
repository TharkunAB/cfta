import MicroCFTA.InternedActualProbeTags

/-!
# The actual three-call source schedule derives exact body tags

The proof starts with the source table invariant before the first probe.
It executes both normalized probes and the reserved fresh body in source
order. Full syntax correspondence supplies every intermediate profile.
No relation between the three returned records is assumed.
-/
namespace MicroCFTA.InternedSourceProbeTags
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedRequestFacts
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedProfiles
open InternedProfileExecutionFacts InternedRootProfile InternedProfileSemantics InternedActualProbeTags
open InternedConstructionProvenance InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeKey)

/-- Arbitrary actual normalized source callbacks derive their profiles from the complete syntax model. -/
theorem callback_profile [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (heap : InternedProfileHeap.Heap state) :
    Checked (callback expression environment name state)
      (fun value => Equivalent (profile value) (normalize name (evaluate expression (some [name] :: environment.map profile)))) :=
  callback_checked expression environment name state normal inputs
    (by simpa only [List.map_cons, profile] using build_profile expression (.reference name :: environment) state normal inputs heap)

/-- The original complete probe and fresh-body calls establish both exact empty and direct-self equivalences. -/
theorem source_calls [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before afterDepth afterOrdinary afterBody : State Symbol Guard)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (normal : Normal before) (inputs : Values before environment) (heap : InternedProfileHeap.Heap before)
    (depthDone : callback expression environment .depth before = .done depth afterDepth)
    (ordinaryDone : callback expression environment (.uninterned depth.depth) afterDepth = .done ordinary afterOrdinary)
    (missing : afterOrdinary.nodes.table (muKey depth ordinary) = none)
    (entrySame : entry = (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).1)
    (bodyDone : callback expression environment (.interned entry.identity)
      {afterOrdinary with nodes := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).2} = .done body afterBody) :
    Tags entry body depth ordinary := by
  have depthInputs : Values before (.reference .depth :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact depth_available before
    · exact inputs value member
  have depthChecked := callback_profile expression environment .depth before normal depthInputs heap
  have depthVerified := callback_verified expression environment .depth before normal.facts depthInputs
  have depthNormal : Normal afterDepth := by
    simpa only [depthDone, Outcome.state] using callback_normal expression environment .depth before normal depthInputs
  have depthHeap : InternedProfileHeap.Heap afterDepth := by simpa only [depthDone, Outcome.state] using depthChecked.heap
  have depthAvailable := depthVerified.result depth afterDepth depthDone
  have afterInputs : Values afterDepth environment := by
    intro value member
    simpa only [depthDone, Outcome.state] using depthVerified.available value (inputs value member)
  have ordinaryInputs : Values afterDepth (.reference (.uninterned depth.depth) :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ordinary_available afterDepth depth.depth
    · exact afterInputs value member
  have ordinaryChecked := callback_profile expression environment (.uninterned depth.depth) afterDepth depthNormal ordinaryInputs depthHeap
  have ordinaryVerified := callback_verified expression environment (.uninterned depth.depth) afterDepth depthNormal.facts ordinaryInputs
  have ordinaryNormal : Normal afterOrdinary := by
    simpa only [ordinaryDone, Outcome.state] using callback_normal expression environment (.uninterned depth.depth) afterDepth depthNormal ordinaryInputs
  have ordinaryHeap : InternedProfileHeap.Heap afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryChecked.heap
  have ordinaryAvailable := ordinaryVerified.result ordinary afterOrdinary ordinaryDone
  have depthLater : Available afterOrdinary depth := by simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth depthAvailable
  have finalInputs : Values afterOrdinary environment := by
    intro value member
    simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available value (afterInputs value member)
  let allocated := {afterOrdinary with nodes := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).2}
  have reserved : Normal allocated := reserve_normal (muKey depth ordinary) afterOrdinary ordinaryNormal
  have growth : Grows afterOrdinary allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have history := intern_issued_extends afterOrdinary.nodes (muKey depth ordinary) ordinaryNormal.facts.coherent.valid.2
  have allocatedInputs : Values allocated environment :=
    fun value member => (finalInputs value member).grows afterOrdinary allocated growth history
  have argument : Available allocated (.reference (.interned entry.identity)) := by
    rw [entrySame]
    exact (reserve_available (muKey depth ordinary) afterOrdinary ordinaryNormal.facts.coherent ordinaryNormal.facts.cached).2
  have bodyInputs : Values allocated (.reference (.interned entry.identity) :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact argument
    · exact allocatedInputs value member
  have bodyChecked := callback_profile expression environment (.interned entry.identity) allocated reserved bodyInputs ordinaryHeap
  have bodyVerified := callback_verified expression environment (.interned entry.identity) allocated reserved.facts bodyInputs
  have actualDone : callback expression environment (.interned entry.identity) allocated = .done body afterBody := bodyDone
  have bodyNormal : Normal afterBody := by
    simpa only [actualDone, Outcome.state] using callback_normal expression environment (.interned entry.identity) allocated reserved bodyInputs
  have actualBody := bodyVerified.result body afterBody bodyDone
  have actualDepth : Available afterBody depth := by
    simpa only [actualDone, Outcome.state] using bodyVerified.available depth (depthLater.grows afterOrdinary allocated growth history)
  have actualOrdinary : Available afterBody ordinary := by
    simpa only [actualDone, Outcome.state] using bodyVerified.available ordinary (ordinaryAvailable.grows afterOrdinary allocated growth history)
  have fresh : ∀ value ∈ environment.map profile, .interned entry.identity ∉ value.getD [] := by
    rw [entrySame]
    exact fresh_profiles depth ordinary environment afterOrdinary ordinaryNormal.facts finalInputs missing
  exact from_profiles expression (environment.map profile) entry body depth ordinary afterBody bodyNormal
    actualBody actualDepth actualOrdinary fresh (depthChecked.result depth afterDepth depthDone)
    (ordinaryChecked.result ordinary afterOrdinary ordinaryDone) (bodyChecked.result body afterBody bodyDone)

end MicroCFTA.InternedSourceProbeTags
