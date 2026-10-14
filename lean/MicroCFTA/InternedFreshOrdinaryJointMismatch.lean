import MicroCFTA.InternedFreshOrdinaryRouteInputs

/-!
# Live ordinary mismatch on the exact repaired pending route

The earlier completed route supplies an actual different request pair.
Agreement on every live varying input would make the later request complete.
Fresh interned changes contradict the original probe's issued-name bound.
The remaining changed input is an actual ordinary crossing on both routes.
-/
namespace MicroCFTA.InternedFreshOrdinaryJointMismatch
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (depth_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryActiveOrigins
open InternedFreshOrdinaryActiveSite InternedFreshOrdinaryActiveReplay
open InternedFreshOrdinaryEarlierPair InternedFreshOrdinaryLiveInputs
open InternedFreshOrdinaryLiveInputSupport InternedFreshOrdinaryRouteInputs
open InternedBinderProtocol (Reference NodeKey)

/-- Each ordinary name in the original Depth probe comes from one actual earlier captured value. -/
theorem Origin.ordinary_capture [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (level : Nat) (member : .uninterned level ∈ origin.depth.free) :
    ∃ value ∈ origin.environment, .uninterned level ∈ value.free := by
  have captured := (InternedFreshOrdinarySourceFreeNames.callback_other origin.body origin.environment .depth
    origin.before origin.context.normal (origin.context.local .depth (depth_available origin.before)).inputs
    origin.context.freeNames origin.context.profiles origin.depth origin.afterDepth origin.depthDone
    (.uninterned level) (by intro impossible; cases impossible)).mp member
  obtain ⟨names, supplied, included⟩ := InternedFreeNameForm.captures_origins origin.body
    (origin.environment.map InternedRootProfile.profile) (origin.environment.map Value.free) (.uninterned level) captured
  obtain ⟨value, present, same⟩ := List.mem_map.mp supplied
  exact ⟨value, present, same ▸ included⟩

/-- The exact earlier route retains a live changed ordinary crossing and its strict capture bound. -/
def Mismatch [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) : Prop :=
  ∃ earlier : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard), ∃ start previous finish,
    earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
      site.crossings.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
    build (.binder site.smart site.body)
      (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
      start = .done previous finish ∧
    Context start (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment) ∧
    Grows finish origin.cut ∧
    InternedFreshOrdinaryProbeChoiceSites.Captures (.reference .depth :: origin.environment) earlier ∧
    (∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut) ∧
    ∃ oldDepth afterDepth oldOrdinary afterOrdinary record,
      callback site.body
        (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
        .depth start = .done oldDepth afterDepth ∧
      callback site.body
        (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
        (.uninterned (ordinaryLevel oldDepth)) afterDepth = .done oldOrdinary afterOrdinary ∧
      InternedNestedConstruction.request site.smart oldDepth oldOrdinary
        (callback site.body (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment))
        afterOrdinary = .done previous finish ∧
      origin.cut.nodeRecords (muKey oldDepth oldOrdinary) = some record ∧
      (oldDepth.referenceOf ≠ origin.depth.referenceOf ∨ oldOrdinary.referenceOf ≠ origin.ordinary.referenceOf) ∧
      ∃ (index : Nat) (first : InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard)
        (second : Crossing Symbol Guard) (level : Nat),
        earlier[index]? = some first ∧ site.crossings[index]? = some second ∧
        first.body = second.body ∧ first.ordinary = true ∧ second.name = .uninterned level ∧
        ordinaryLevel first.depth ≠ level ∧
        .inr (.uninterned (ordinaryLevel first.depth), .uninterned level) ∈
          liveInputs (.binder site.smart site.body) (routeInputs origin earlier site.crossings) ∧
        .uninterned level ∈ origin.depth.free ∧ level < ordinaryLevel origin.depth ∧
        ∃ value ∈ origin.environment, .uninterned level ∈ value.free

/-- Every actual repaired pending site derives a changed live ordinary input on its actual earlier completed route. -/
theorem Site.mismatch [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) : Mismatch site := by
  classical
  obtain ⟨earlier, start, previous, finish, descriptors, previousDone, previousContext, _, suffix, captures, traces,
    oldDepth, afterDepth, oldOrdinary, afterOrdinary, record, oldDepthDone, oldOrdinaryDone, oldRequestDone, oldStored, oldDifferent⟩ :=
    InternedFreshOrdinaryEarlierPair.Site.scoped_earlier_pair site
  have lengths : earlier.length = site.crossings.length := by
    simpa only [List.length_map] using congrArg List.length descriptors
  have values := route_values origin earlier site.crossings lengths
  have actualValues : (routeInputs origin earlier site.crossings).map (input Prod.snd) = site.environment :=
    values.2.trans site.inputs.symm
  have depthGrowth : Grows site.before site.afterDepth := by
    simpa only [site.depthDone, Outcome.state] using
      (callback_growing site.body site.environment .depth site.before site.context.normal.facts.coherent.valid).2
  have ordinaryGrowth : Grows site.afterDepth final := by
    simpa only [site.ordinaryDone, Outcome.state] using
      (callback_growing site.body site.environment (.uninterned (ordinaryLevel origin.depth))
        site.afterDepth site.depthContext.normal.facts.coherent.valid).2
  have cutAllocated : Grows origin.cut origin.allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have cutFinal := grows_trans cutAllocated (grows_trans site.initial (grows_trans depthGrowth ordinaryGrowth))
  have differs : ∃ label ∈ liveInputs (.binder site.smart site.body) (routeInputs origin earlier site.crossings),
      Sum.elim id Prod.fst label ≠ Sum.elim id Prod.snd label := by
    apply Classical.byContradiction
    intro none
    have agree : ∀ label ∈ liveInputs (.binder site.smart site.body) (routeInputs origin earlier site.crossings),
        Sum.elim id Prod.fst label = Sum.elim id Prod.snd label := by
      intro label included
      apply Classical.byContradiction
      intro different
      exact none ⟨label, included, different⟩
    have ready := InternedFreshOrdinaryLiveInputReadiness.not_pending_after_probes site.smart site.body
      (routeInputs origin earlier site.crossings) Prod.fst Prod.snd agree start site.before finish site.afterDepth final
      (by simpa only [values.1] using previousContext) (by simpa only [actualValues] using site.context)
      previous origin.depth origin.ordinary (by simpa only [values.1] using previousDone)
      (by simpa only [actualValues] using site.depthDone) (by simpa only [actualValues] using site.ordinaryDone)
      (grows_trans suffix cutFinal)
    exact ready (origin.sameKey ▸ site.pending)
  obtain ⟨label, live, different⟩ := differs
  cases label with
  | inl fixed => exact False.elim (different rfl)
  | inr atom =>
      have included := route_member origin earlier site.crossings atom
        (live_member (.binder site.smart site.body) (routeInputs origin earlier site.crossings) atom live)
      obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.mp included
      have fresh : ∀ crossing ∈ site.crossings, ∀ identity, crossing.name = .interned identity → origin.cut.nodes.next ≤ identity :=
        fun crossing member identity same => Crossing.interned_after origin crossing (site.traces crossing member).1 identity same
      have supported : ∀ name, name ≠ .depth → atom.2 = name → name ∈ origin.depth.free := by
        intro name notDepth same
        have actual := callback_live site.smart site.body (routeInputs origin earlier site.crossings) Prod.snd .depth
          site.before site.afterDepth (by simpa only [actualValues] using site.context) (depth_available site.before)
          origin.depth (by simpa only [actualValues] using site.depthDone) (.inr atom) live (by simpa only [Sum.elim_inr, same] using notDepth)
        simpa only [Sum.elim_inr, same] using actual
      rcases routeAtoms_changed origin earlier site.crossings descriptors fresh index atom atIndex different with
        ⟨identity, recent, named⟩ | ⟨first, second, level, firstAt, secondAt, bodies, flag, named, unequal, atomSame⟩
      · have present := supported (.interned identity) (by intro impossible; cases impossible) named
        have old := InternedFreshProbeKeys.issued_free_below origin.cut.nodes origin.cutContext.normal.facts.coherent.valid.2
          origin.depth origin.depthAvailable.issued identity present
        omega
      · have present := supported (.uninterned level) (by intro impossible; cases impossible) (by rw [atomSame])
        exact ⟨earlier, start, previous, finish, descriptors, previousDone, previousContext, suffix, captures, traces,
          oldDepth, afterDepth, oldOrdinary, afterOrdinary, record, oldDepthDone, oldOrdinaryDone, oldRequestDone, oldStored, oldDifferent,
          index, first, second, level, firstAt, secondAt, bodies, flag, named, unequal,
          atomSame ▸ live, present, ordinary_free_bound origin.depth level present,
          InternedFreshOrdinaryJointMismatch.Origin.ordinary_capture origin level present⟩

/-- Actual closed repaired pending execution supplies the full ordinary mismatch without a supplied source site. -/
theorem closed_mismatch [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : Site origin final, Mismatch site := by
  obtain ⟨origin, ⟨site⟩⟩ := InternedFreshOrdinaryActiveSite.encounter_site key final
    (InternedFreshOrdinaryActiveEncounter.closed_encounter expression key final pending)
  exact ⟨origin, site, InternedFreshOrdinaryJointMismatch.Site.mismatch site⟩

end MicroCFTA.InternedFreshOrdinaryJointMismatch
