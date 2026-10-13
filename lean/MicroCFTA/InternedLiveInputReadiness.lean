import MicroCFTA.InternedLiveInputReplay

/-!
# Completed source sites exclude later pending readback

An earlier completed binder supplies both canonical probes and the complete
request. A later call with the same live lexical inputs reuses that request
after its two actual probes complete. The later binder need not be complete.
-/
namespace MicroCFTA.InternedLiveInputReadiness
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedSpecialization
open InternedFreeAbsenceContext InternedLiveInputContext InternedLiveInputReplay
open InternedRequestAgreement InternedNestedErasureReplay
open InternedBinderProtocol (Reference NodeKey)

/-- An earlier completed binder makes the later actual request complete after its probes finish. -/
theorem request_after_probes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (atoms : List Atom) (firstMap secondMap : Atom → Reference)
    (agree : ∀ atom ∈ liveInputs (.binder smart body) atoms, firstMap atom = secondMap atom)
    (left right afterLeft afterRightDepth afterRight : State Symbol Guard)
    (lc : Context left (atoms.map firstMap)) (rc : Context right (atoms.map secondMap))
    (first depth ordinary : Value Symbol Guard)
    (firstDone : build (.binder smart body) ((atoms.map firstMap).map Value.reference) left = .done first afterLeft)
    (depthDone : callback body ((atoms.map secondMap).map Value.reference) .depth right = .done depth afterRightDepth)
    (ordinaryDone : callback body ((atoms.map secondMap).map Value.reference) (.uninterned depth.depth) afterRightDepth = .done ordinary afterRight)
    (growth : Grows afterLeft afterRight) :
    request smart depth ordinary (callback body ((atoms.map secondMap).map Value.reference)) afterRight = .done first afterRight := by
  rw [build] at firstDone
  change ((callback body ((atoms.map firstMap).map Value.reference) .depth left).bind fun depth middle =>
    (callback body ((atoms.map firstMap).map Value.reference) (.uninterned depth.depth) middle).bind fun ordinary beforeRequest =>
      request smart depth ordinary (callback body ((atoms.map firstMap).map Value.reference)) beforeRequest) = .done first afterLeft at firstDone
  obtain ⟨oldDepth, afterLeftDepth, oldDepthDone, leftLater⟩ := bind_done _ _ _ _ firstDone
  obtain ⟨oldOrdinary, beforeLeftRequest, oldOrdinaryDone, oldRequestDone⟩ := bind_done _ _ _ _ leftLater
  have leftDepthContext : Context afterLeftDepth (atoms.map firstMap) := by
    simpa only [oldDepthDone, Outcome.state] using lc.callback body .depth (depth_available left)
  have rightDepthContext : Context afterRightDepth (atoms.map secondMap) := by
    simpa only [depthDone, Outcome.state] using rc.callback body .depth (depth_available right)
  have leftRequestContext : Context beforeLeftRequest (atoms.map firstMap) := by
    simpa only [oldOrdinaryDone, Outcome.state] using
      leftDepthContext.callback body (.uninterned oldDepth.depth) (ordinary_available afterLeftDepth oldDepth.depth)
  have rightRequestContext : Context afterRight (atoms.map secondMap) := by
    simpa only [ordinaryDone, Outcome.state] using
      rightDepthContext.callback body (.uninterned depth.depth) (ordinary_available afterRightDepth depth.depth)
  have leftRequestGrowth : Grows beforeLeftRequest afterLeft := by
    simpa only [oldRequestDone, Outcome.state] using
      (request_correct smart oldDepth oldOrdinary _ (callback_growing body ((atoms.map firstMap).map Value.reference))
        beforeLeftRequest leftRequestContext.normal.facts.coherent.valid).2
  have leftOrdinaryGrowth : Grows afterLeftDepth beforeLeftRequest := by
    simpa only [oldOrdinaryDone, Outcome.state] using
      (callback_growing body ((atoms.map firstMap).map Value.reference) (.uninterned oldDepth.depth)
        afterLeftDepth leftDepthContext.normal.facts.coherent.valid).2
  have rightOrdinaryGrowth : Grows afterRightDepth afterRight := by
    simpa only [ordinaryDone, Outcome.state] using
      (callback_growing body ((atoms.map secondMap).map Value.reference) (.uninterned depth.depth)
        afterRightDepth rightDepthContext.normal.facts.coherent.valid).2
  have depthSame := callback_same body (build_same body) smart atoms firstMap secondMap .depth
    agree left right afterRight afterLeftDepth afterRightDepth lc rc rightRequestContext.normal.facts.coherent
    (depth_available left) (depth_available right) oldDepth depth oldDepthDone depthDone
    (grows_trans leftOrdinaryGrowth (grows_trans leftRequestGrowth growth)) rightOrdinaryGrowth
  subst oldDepth
  have ordinarySame := callback_same body (build_same body) smart atoms firstMap secondMap
    (.uninterned depth.depth) agree afterLeftDepth afterRightDepth afterRight beforeLeftRequest afterRight
    leftDepthContext rightDepthContext rightRequestContext.normal.facts.coherent
    (ordinary_available afterLeftDepth depth.depth) (ordinary_available afterRightDepth depth.depth)
    oldOrdinary ordinary oldOrdinaryDone ordinaryDone (grows_trans leftRequestGrowth growth) (grows_refl _)
  subst oldOrdinary
  exact request_after_done smart depth ordinary (callback body ((atoms.map firstMap).map Value.reference))
    (callback body ((atoms.map secondMap).map Value.reference)) beforeLeftRequest afterRight first afterLeft
    leftRequestContext.normal.facts.coherent.valid (callback_growing body ((atoms.map firstMap).map Value.reference))
    oldRequestDone growth

/-- The later binder completes once its actual probes complete and a matching live-input site exists. -/
theorem binder_after_probes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (atoms : List Atom) (firstMap secondMap : Atom → Reference)
    (agree : ∀ atom ∈ liveInputs (.binder smart body) atoms, firstMap atom = secondMap atom)
    (left right afterLeft afterRightDepth afterRight : State Symbol Guard)
    (lc : Context left (atoms.map firstMap)) (rc : Context right (atoms.map secondMap))
    (first depth ordinary : Value Symbol Guard)
    (firstDone : build (.binder smart body) ((atoms.map firstMap).map Value.reference) left = .done first afterLeft)
    (depthDone : callback body ((atoms.map secondMap).map Value.reference) .depth right = .done depth afterRightDepth)
    (ordinaryDone : callback body ((atoms.map secondMap).map Value.reference) (.uninterned depth.depth) afterRightDepth = .done ordinary afterRight)
    (growth : Grows afterLeft afterRight) :
    build (.binder smart body) ((atoms.map secondMap).map Value.reference) right = .done first afterRight := by
  have ready := request_after_probes smart body atoms firstMap secondMap agree left right afterLeft afterRightDepth afterRight
    lc rc first depth ordinary firstDone depthDone ordinaryDone growth
  rw [build]
  change ((callback body ((atoms.map secondMap).map Value.reference) .depth right).bind fun depth middle =>
    (callback body ((atoms.map secondMap).map Value.reference) (.uninterned depth.depth) middle).bind fun ordinary beforeRequest =>
      request smart depth ordinary (callback body ((atoms.map secondMap).map Value.reference)) beforeRequest) = .done first afterRight
  simpa only [depthDone, Outcome.bind, ordinaryDone] using ready

/-- A complete matching site excludes the exact missing-record condition after the later probes. -/
theorem not_pending_after_probes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (atoms : List Atom) (firstMap secondMap : Atom → Reference)
    (agree : ∀ atom ∈ liveInputs (.binder smart body) atoms, firstMap atom = secondMap atom)
    (left right afterLeft afterRightDepth afterRight : State Symbol Guard)
    (lc : Context left (atoms.map firstMap)) (rc : Context right (atoms.map secondMap))
    (first depth ordinary : Value Symbol Guard)
    (firstDone : build (.binder smart body) ((atoms.map firstMap).map Value.reference) left = .done first afterLeft)
    (depthDone : callback body ((atoms.map secondMap).map Value.reference) .depth right = .done depth afterRightDepth)
    (ordinaryDone : callback body ((atoms.map secondMap).map Value.reference) (.uninterned depth.depth) afterRightDepth = .done ordinary afterRight)
    (growth : Grows afterLeft afterRight) : ¬ IsPending (muKey depth ordinary) afterRight := by
  have ready := request_after_probes smart body atoms firstMap secondMap agree left right afterLeft afterRightDepth afterRight
    lc rc first depth ordinary firstDone depthDone ordinaryDone growth
  rintro ⟨⟨entry, found⟩, missing⟩
  simp only [request, found, missing] at ready
  cases ready

end MicroCFTA.InternedLiveInputReadiness
