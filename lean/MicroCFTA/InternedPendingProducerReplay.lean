import MicroCFTA.InternedPendingProducerPaths
import MicroCFTA.InternedPendingJointKeyMismatch

/-!
# Completed source representatives inside ordinary-name producers

The producer's completed Depth callback executes the same syntactic route.
It therefore contains a completed representative of the later active binder.
This theorem uses one actual producer callback and does not posit another.
-/
namespace MicroCFTA.InternedPendingProducerReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedMissReadback InternedStoredMuOrigins
open InternedNestedSpecialization
open InternedFreeAbsenceContext InternedActiveSourceOrigins InternedActiveSourceReplay
open InternedRequestAgreement InternedFreshProbeKeys InternedPendingJointKey
open InternedOrdinaryProducerPaths InternedPendingJointKeyMismatch
open InternedBinderProtocol (Reference NodeKey)

/-- Closed execution identifies both current callback results with the actual original probe records. -/
theorem closed_site [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ _site : Site origin final, Inputs (.binder origin.smart origin.body) origin.names origin.before := by
  obtain ⟨origin, smart, body, names, before, depth, afterDepth, ordinary, crossings,
    captures, context, path, initial, traces, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable, sameKey, waiting⟩ :=
    InternedPendingProducerPaths.closed_encounter expression key final pending
  have depthContext : Context afterDepth names := by
    simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
  have finalContext : Context final names := by
    simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned depth.depth) (ordinary_available afterDepth depth.depth)
  have depthGrowth : Grows before afterDepth := by
    simpa only [depthDone, Outcome.state] using
      (callback_growing body (names.map Value.reference) .depth before context.normal.facts.coherent.valid).2
  have ordinaryGrowth : Grows afterDepth final := by
    simpa only [ordinaryDone, Outcome.state] using
      (callback_growing body (names.map Value.reference) (.uninterned depth.depth) afterDepth depthContext.normal.facts.coherent.valid).2
  have allocated : Grows origin.cut origin.allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have cutGrowth := grows_trans allocated (grows_trans initial (grows_trans depthGrowth ordinaryGrowth))
  have keys : depth.referenceOf = origin.depth.referenceOf ∧ ordinary.referenceOf = origin.ordinary.referenceOf := by
    simpa only [muKey, NodeKey.mu.injEq, InternedBinderProtocol.MuKey.mk.injEq] using sameKey.symm.trans origin.sameKey
  have depthSame := resident_reference_injective final finalContext.normal.facts.coherent depth origin.depth
    depthAvailable.resident (resident_grows origin.cut final cutGrowth origin.depth origin.depthAvailable.resident) keys.1
  have ordinarySame := resident_reference_injective final finalContext.normal.facts.coherent ordinary origin.ordinary
    ordinaryAvailable.resident (resident_grows origin.cut final cutGrowth origin.ordinary origin.ordinaryAvailable.resident) keys.2
  exact ⟨origin, ⟨smart, body, names, before, afterDepth, crossings, captures.origins, context, path, initial, traces,
    by simpa only [depthSame] using depthDone,
    by simpa only [depthSame, ordinarySame] using ordinaryDone, waiting⟩, captures⟩

/-- The exact current and earlier pairs retain the stronger enclosing-producer invariant. -/
theorem closed_joint_mismatch [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : Site origin final,
      Inputs (.binder origin.smart origin.body) origin.names origin.before ∧ Mismatch site := by
  obtain ⟨origin, site, inputs⟩ := closed_site expression key final pending
  exact ⟨origin, site, inputs, Site.mismatch site⟩

/-- The producer's earlier Depth call contains a completed representative along the same source route. -/
theorem producer_representative [DecidableEq (EdgeKey Symbol Guard)] (producer : Crossing Symbol Guard)
    (level : Nat) (named : producer.name = .uninterned level)
    {target : Syntax Symbol Guard} {names : List Reference} {crossings : List (Crossing Symbol Guard)}
    (path : Path producer.body (producer.name :: producer.names) target names crossings) :
    ∃ earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard), ∃ start value finish,
      earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
        crossings.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
      build target ((earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: producer.names).map Value.reference)
        start = .done value finish ∧
      Context start (earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: producer.names) ∧
      Grows producer.before start ∧ Grows finish producer.start ∧
      ∀ crossing ∈ earlier, Grows producer.before crossing.before ∧ Grows crossing.afterDepth producer.start := by
  obtain ⟨depth, depthDone, _⟩ := InternedPendingOrdinaryMismatch.ordinary_readback producer level named
  obtain ⟨raw, afterRaw, rawDone, filterDone⟩ := bind_done _ _ _ _ depthDone
  have localContext := producer.context.local .depth (depth_available producer.before)
  have afterContext : Context afterRaw (.depth :: producer.names) := by
    simpa only [List.map_cons, rawDone, Outcome.state] using localContext.build producer.body
  have filterGrowth : Grows afterRaw producer.start := by
    simpa only [filterDone, Outcome.state] using
      (work_correct (withoutSelfReference .depth raw) afterRaw afterContext.normal.facts.coherent.valid).2
  obtain ⟨earlier, start, value, finish, descriptors, done, context, initial, suffix, traces⟩ :=
    InternedProbeChoiceSites.completed_route (InternedActiveSourceReplay.Path.probe_route path)
      (.depth :: producer.names) producer.before afterRaw raw localContext
      (by simpa only [List.map_cons] using rawDone)
  exact ⟨earlier, start, value, finish, descriptors, done, context, initial, grows_trans suffix filterGrowth,
    fun crossing member => ⟨(traces crossing member).1, grows_trans (traces crossing member).2 filterGrowth⟩⟩

/-- Every ordinary capture of the active binder yields an earlier completed copy inside its producer. -/
theorem earlier_ancestor [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (inputs : Inputs (.binder origin.smart origin.body) origin.names origin.before)
    (level : Nat) (member : .uninterned level ∈ origin.names) :
    ∃ producer : Crossing Symbol Guard, ∃ crossings,
    ∃ earlier : List (InternedProbeChoiceSites.Crossing Symbol Guard), ∃ start value finish,
      producer.name = .uninterned level ∧
      Path producer.body (.uninterned level :: producer.names) (.binder origin.smart origin.body) origin.names crossings ∧
      origin.names = crossings.map Crossing.name ++ .uninterned level :: producer.names ∧
      producer.names.length < origin.names.length ∧
      earlier.map (fun crossing : InternedProbeChoiceSites.Crossing Symbol Guard => (crossing.body, crossing.ordinary)) =
        crossings.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
      build (.binder origin.smart origin.body)
        ((earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: producer.names).map Value.reference)
        start = .done value finish ∧
      Context start (earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: producer.names) ∧
      Grows producer.before start ∧ Grows finish producer.start ∧ Grows producer.start origin.before ∧
      ∃ oldDepth afterDepth oldOrdinary afterOrdinary record,
        callback origin.body ((earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: producer.names).map Value.reference)
          .depth start = .done oldDepth afterDepth ∧
        callback origin.body ((earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: producer.names).map Value.reference)
          (.uninterned oldDepth.depth) afterDepth = .done oldOrdinary afterOrdinary ∧
        request origin.smart oldDepth oldOrdinary
          (callback origin.body ((earlier.map InternedProbeChoiceSites.Crossing.name ++ .depth :: producer.names).map Value.reference))
          afterOrdinary = .done value finish ∧
        origin.cut.nodeRecords (muKey oldDepth oldOrdinary) = some record ∧
        (oldDepth.referenceOf ≠ origin.depth.referenceOf ∨ oldOrdinary.referenceOf ≠ origin.ordinary.referenceOf) := by
  obtain ⟨producer, crossings, depth, named, path, suffix, shorter, depthDone, same, initial, traces⟩ :=
    inputs.producer level member
  obtain ⟨earlier, start, value, finish, descriptors, done, context, front, back, _⟩ :=
    producer_representative producer level named (by simpa only [named] using path)
  have growth : Grows origin.before origin.cut := by
    have depthGrowth : Grows origin.before origin.afterDepth := by
      simpa only [origin.depthDone, Outcome.state] using
        (callback_growing origin.body (origin.names.map Value.reference) .depth origin.before origin.context.normal.facts.coherent.valid).2
    have depthContext : Context origin.afterDepth origin.names := by
      simpa only [origin.depthDone, Outcome.state] using origin.context.callback origin.body .depth (depth_available origin.before)
    have ordinaryGrowth : Grows origin.afterDepth origin.cut := by
      simpa only [origin.ordinaryDone, Outcome.state] using
        (callback_growing origin.body (origin.names.map Value.reference) (.uninterned origin.depth.depth)
          origin.afterDepth depthContext.normal.facts.coherent.valid).2
    exact grows_trans depthGrowth ordinaryGrowth
  exact ⟨producer, crossings, earlier, start, value, finish, named, path, suffix, shorter,
    descriptors, done, context, front, back, initial,
    earlier_pair origin origin.smart origin.body _ start context value finish done (grows_trans back (grows_trans initial growth))⟩

end MicroCFTA.InternedPendingProducerReplay
