import MicroCFTA.InternedFreshOrdinaryLiveInputReplay

/-!
# Earlier repaired requests exclude later pending readback

A completed earlier binder and agreement on live varying inputs determine
both later actual probes. The later constructor need not have returned.
Fixed captured values remain identical. Cache growth retains the earlier
completed request at its actual pair key.
-/
namespace MicroCFTA.InternedFreshOrdinaryLiveInputReadiness
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work request request_correct IsPending)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedNestedSpecialization InternedNestedErasureReplay
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs InternedFreshOrdinaryLiveInputContext
open InternedFreshOrdinaryLiveInputReplay
open InternedBinderProtocol (Reference NodeKey)

/-- An earlier completed binder makes the later actual request complete after its probes finish. -/
theorem request_after_probes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (agree : ∀ atom ∈ liveInputs (.binder smart body) inputs, Sum.elim id firstNames atom = Sum.elim id secondNames atom)
    (left right afterLeft afterRightDepth afterRight : State Symbol Guard)
    (lc : Context left (inputs.map (input firstNames))) (rc : Context right (inputs.map (input secondNames)))
    (first depth ordinary : Value Symbol Guard)
    (firstDone : build (.binder smart body) (inputs.map (input firstNames)) left = .done first afterLeft)
    (depthDone : callback body (inputs.map (input secondNames)) .depth right = .done depth afterRightDepth)
    (ordinaryDone : callback body (inputs.map (input secondNames)) (.uninterned (ordinaryLevel depth)) afterRightDepth = .done ordinary afterRight)
    (growth : Grows afterLeft afterRight) :
    request smart depth ordinary (callback body (inputs.map (input secondNames))) afterRight = .done first afterRight := by
  rw [build] at firstDone
  change ((callback body (inputs.map (input firstNames)) .depth left).bind fun depth middle =>
    (callback body (inputs.map (input firstNames)) (.uninterned (ordinaryLevel depth)) middle).bind fun ordinary beforeRequest =>
      request smart depth ordinary (callback body (inputs.map (input firstNames))) beforeRequest) = .done first afterLeft at firstDone
  obtain ⟨oldDepth, afterLeftDepth, oldDepthDone, leftLater⟩ := bind_done _ _ _ _ firstDone
  obtain ⟨oldOrdinary, beforeLeftRequest, oldOrdinaryDone, oldRequestDone⟩ := bind_done _ _ _ _ leftLater
  have leftDepthContext : Context afterLeftDepth (inputs.map (input firstNames)) := by
    simpa only [oldDepthDone, Outcome.state] using lc.callback body .depth (depth_available left)
  have rightDepthContext : Context afterRightDepth (inputs.map (input secondNames)) := by
    simpa only [depthDone, Outcome.state] using rc.callback body .depth (depth_available right)
  have leftRequestContext : Context beforeLeftRequest (inputs.map (input firstNames)) := by
    simpa only [oldOrdinaryDone, Outcome.state] using
      leftDepthContext.callback body (.uninterned (ordinaryLevel oldDepth)) (ordinary_available afterLeftDepth (ordinaryLevel oldDepth))
  have rightRequestContext : Context afterRight (inputs.map (input secondNames)) := by
    simpa only [ordinaryDone, Outcome.state] using
      rightDepthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterRightDepth (ordinaryLevel depth))
  have leftRequestGrowth : Grows beforeLeftRequest afterLeft := by
    simpa only [oldRequestDone, Outcome.state] using
      (request_correct smart oldDepth oldOrdinary _ (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input firstNames)))
        beforeLeftRequest leftRequestContext.normal.facts.coherent.valid).2
  have leftOrdinaryGrowth : Grows afterLeftDepth beforeLeftRequest := by
    simpa only [oldOrdinaryDone, Outcome.state] using
      (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input firstNames)) (.uninterned (ordinaryLevel oldDepth))
        afterLeftDepth leftDepthContext.normal.facts.coherent.valid).2
  have rightOrdinaryGrowth : Grows afterRightDepth afterRight := by
    simpa only [ordinaryDone, Outcome.state] using
      (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input secondNames)) (.uninterned (ordinaryLevel depth))
        afterRightDepth rightDepthContext.normal.facts.coherent.valid).2
  have depthSame := callback_same body (build_same body) smart inputs firstNames secondNames .depth
    agree left right afterRight afterLeftDepth afterRightDepth lc rc rightRequestContext.normal.facts.coherent
    (depth_available left) (depth_available right) oldDepth depth oldDepthDone depthDone
    (grows_trans leftOrdinaryGrowth (grows_trans leftRequestGrowth growth)) rightOrdinaryGrowth
  subst oldDepth
  have ordinarySame := callback_same body (build_same body) smart inputs firstNames secondNames
    (.uninterned (ordinaryLevel depth)) agree afterLeftDepth afterRightDepth afterRight beforeLeftRequest afterRight
    leftDepthContext rightDepthContext rightRequestContext.normal.facts.coherent
    (ordinary_available afterLeftDepth (ordinaryLevel depth)) (ordinary_available afterRightDepth (ordinaryLevel depth))
    oldOrdinary ordinary oldOrdinaryDone ordinaryDone (grows_trans leftRequestGrowth growth) (grows_refl _)
  subst oldOrdinary
  exact request_after_done smart depth ordinary (callback body (inputs.map (input firstNames)))
    (callback body (inputs.map (input secondNames))) beforeLeftRequest afterRight first afterLeft
    leftRequestContext.normal.facts.coherent.valid (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input firstNames)))
    oldRequestDone growth

/-- A complete matching site excludes the exact missing-record condition after the later probes. -/
theorem not_pending_after_probes [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (agree : ∀ atom ∈ liveInputs (.binder smart body) inputs, Sum.elim id firstNames atom = Sum.elim id secondNames atom)
    (left right afterLeft afterRightDepth afterRight : State Symbol Guard)
    (lc : Context left (inputs.map (input firstNames))) (rc : Context right (inputs.map (input secondNames)))
    (first depth ordinary : Value Symbol Guard)
    (firstDone : build (.binder smart body) (inputs.map (input firstNames)) left = .done first afterLeft)
    (depthDone : callback body (inputs.map (input secondNames)) .depth right = .done depth afterRightDepth)
    (ordinaryDone : callback body (inputs.map (input secondNames)) (.uninterned (ordinaryLevel depth)) afterRightDepth = .done ordinary afterRight)
    (growth : Grows afterLeft afterRight) : ¬ IsPending (muKey depth ordinary) afterRight := by
  have ready := request_after_probes smart body inputs firstNames secondNames agree left right afterLeft afterRightDepth afterRight
    lc rc first depth ordinary firstDone depthDone ordinaryDone growth
  rintro ⟨⟨entry, found⟩, missing⟩
  simp only [request, found, missing] at ready
  cases ready

end MicroCFTA.InternedFreshOrdinaryLiveInputReadiness
