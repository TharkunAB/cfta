import MicroCFTA.InternedPendingProducerCalls
import MicroCFTA.InternedPendingJointKeyMismatch

/-!
# Actual enclosing pending calls with shorter captured environments

Each producer retains its completed Depth callback and stopped ordinary call.
The whole enclosing binder stops at the same request and final state.
The request key was absent when the producer started.
-/
namespace MicroCFTA.InternedPendingProducerDescent
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedMissReadback InternedStoredMuOrigins
open InternedNestedSpecialization
open InternedFreeAbsenceContext InternedActiveSourceOrigins InternedActiveSourceReplay
open InternedRequestAgreement InternedFreshProbeKeys InternedPendingJointKey
open InternedOrdinaryProducerCalls InternedPendingJointKeyMismatch
open InternedBinderProtocol (Reference NodeKey)

/-- Closed execution identifies both current callback results with the actual original probe records. -/
theorem closed_site [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ _site : Site origin final, Inputs key final (.binder origin.smart origin.body) origin.names origin.before := by
  obtain ⟨origin, smart, body, names, before, depth, afterDepth, ordinary, crossings,
    captures, context, path, initial, traces, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable, sameKey, waiting⟩ :=
    InternedPendingProducerCalls.closed_encounter expression key final pending
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
  exact ⟨origin, ⟨smart, body, names, before, afterDepth, crossings, captures.paths.origins, context, path, initial, traces,
    by simpa only [depthSame] using depthDone,
    by simpa only [depthSame, ordinarySame] using ordinaryDone, waiting⟩, captures⟩

/-- The exact current and earlier pairs retain the stronger enclosing-producer invariant. -/
theorem closed_joint_mismatch [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : Site origin final,
      Inputs key final (.binder origin.smart origin.body) origin.names origin.before ∧ Mismatch site := by
  obtain ⟨origin, site, inputs⟩ := closed_site expression key final pending
  exact ⟨origin, site, inputs, Site.mismatch site⟩

/-- An enclosing ordinary producer has a completed Depth call and the same actual pending outcome. -/
def EnclosingAt [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (final : State Symbol Guard) (index level : Nat) : Prop :=
  ∃ producer : Crossing Symbol Guard, ∃ crossings depth,
    producer.name = .uninterned level ∧
    Path producer.body (.uninterned level :: producer.names) (.binder origin.smart origin.body) origin.names crossings ∧
    crossings.length = index ∧
    origin.names = crossings.map Crossing.name ++ .uninterned level :: producer.names ∧
    producer.names.length < origin.names.length ∧
    callback producer.body (producer.names.map Value.reference) .depth producer.before = .done depth producer.start ∧
    depth.depth = level ∧
    callback producer.body (producer.names.map Value.reference) (.uninterned level) producer.start = .pending key final ∧
    build (.binder producer.smart producer.body) (producer.names.map Value.reference) producer.before = .pending key final ∧
    Grows producer.start origin.before ∧
    producer.before.nodes.table key = none ∧ producer.start.nodes.table key = none ∧
    ¬ Grows origin.allocated producer.start

/-- Each captured ordinary name derives its enclosing pending execution at an earlier cache cut. -/
theorem enclosing_pending_at [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (inputs : Inputs key final (.binder origin.smart origin.body) origin.names origin.before)
    (index level : Nat) (member : origin.names[index]? = some (.uninterned level)) : EnclosingAt origin final index level := by
  obtain ⟨producer, crossings, named, path, position, initial, traces, stopped⟩ := inputs index level member
  obtain ⟨depth, depthDone, same⟩ := InternedPendingOrdinaryMismatch.ordinary_readback producer level named
  have suffix := InternedActiveSourceReplay.Path.names path
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
  have missing : producer.start.nodes.table key = none := by
    cases found : producer.start.nodes.table key with
    | none => rfl
    | some entry =>
        have retained := (grows_trans initial growth).nodes key entry found
        rw [origin.missing] at retained
        cases retained
  have originalMissing : producer.before.nodes.table key = none := by
    cases found : producer.before.nodes.table key with
    | none => rfl
    | some entry =>
        have retained := producer.facts.2.nodes key entry found
        rw [missing] at retained
        cases retained
  have ordinaryStopped : callback producer.body (producer.names.map Value.reference) (.uninterned level) producer.start = .pending key final := by
    simpa only [named] using stopped
  refine ⟨producer, crossings, depth, named, by simpa only [named] using path,
    position, by simpa only [named] using suffix, ?_, depthDone, same, ordinaryStopped, ?_, initial, originalMissing, missing, ?_⟩
  · rw [suffix, List.length_append, List.length_cons]
    omega
  · rw [build]
    change ((callback producer.body (producer.names.map Value.reference) .depth producer.before).bind _) = .pending key final
    rw [depthDone]
    change ((callback producer.body (producer.names.map Value.reference) (.uninterned depth.depth) producer.start).bind _) = .pending key final
    rw [same, ordinaryStopped]
    rfl
  · intro reversed
    have installed : origin.allocated.nodes.table key = some origin.entry :=
      (Cache.intern_correct origin.cut.nodes key origin.cutContext.normal.facts.coherent.valid.2).2.1
    have retained := reversed.nodes key origin.entry installed
    rw [missing] at retained
    cases retained

/-- The live mismatch selects an actual shorter enclosing pending call while retaining both key components. -/
theorem closed_enclosing_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : Site origin final,
      Inputs key final (.binder origin.smart origin.body) origin.names origin.before ∧
      Mismatch site ∧ ∃ index level,
        ((.uninterned level), index) ∈ InternedLiveInputContext.liveInputs (.binder origin.smart origin.body) origin.names.zipIdx ∧
        EnclosingAt origin final index level := by
  obtain ⟨origin, site, inputs, mismatch⟩ := closed_joint_mismatch expression key final pending
  obtain ⟨earlier, start, previous, finish, descriptors, previousDone, context, suffix, traces,
    oldDepth, afterDepth, oldOrdinary, afterOrdinary, record, oldDepthDone, oldOrdinaryDone, requested, stored, different,
    index, first, second, level, firstAt, secondAt, bodySame, ordinary, named, changed, live, present, captured, producer⟩ := mismatch
  have mapped := InternedLiveInputSupport.liveInputs_map (.binder origin.smart origin.body) origin.names.zipIdx Prod.fst
  rw [List.zipIdx_map_fst] at mapped
  rw [mapped] at captured
  obtain ⟨atom, atomLive, atomName⟩ := List.mem_map.mp captured
  have atomAt := List.mem_zipIdx_iff_getElem?.mp (InternedLiveInputSupport.liveInputs_member _ _ _ atomLive)
  refine ⟨origin, site, inputs, Site.mismatch site, atom.2, level, ?_, ?_⟩
  · simpa only [← atomName] using atomLive
  · exact enclosing_pending_at origin inputs atom.2 level (by simpa only [atomName] using atomAt)

end MicroCFTA.InternedPendingProducerDescent
