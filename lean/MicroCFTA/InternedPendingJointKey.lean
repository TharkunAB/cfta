import MicroCFTA.InternedPendingOrdinaryOrigins

/-!
# Both original probe records at a pending source site

The actual pending key identifies both complete original probe records.
The two current callbacks return those exact records. Decoding both probes
then gives equality of the complete live captured-name sets, including
Depth and the original ordinary sentinel.
-/
namespace MicroCFTA.InternedPendingJointKey
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedMissReadback InternedStoredMuOrigins
open InternedFreeAbsenceContext InternedActiveSourceOrigins InternedActiveSourceReplay
open InternedLiveInputContext InternedLiveInputSupport InternedRequestAgreement InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeKey)

/-- An actual stopped source site retains both exact active-ancestor probes. -/
structure Site [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (final : State Symbol Guard) where
  smart : Bool
  body : Syntax Symbol Guard
  names : List Reference
  before : State Symbol Guard
  afterDepth : State Symbol Guard
  crossings : List (Crossing Symbol Guard)
  captures : InternedPendingOrdinaryOrigins.Inputs origin.names origin.before
  context : Context before names
  path : Path origin.body origin.localNames (.binder smart body) names crossings
  initial : Grows origin.allocated before
  traces : ∀ crossing ∈ crossings, Grows origin.allocated crossing.before ∧ Grows crossing.start before
  depthDone : callback body (names.map Value.reference) .depth before = .done origin.depth afterDepth
  ordinaryDone : callback body (names.map Value.reference) (.uninterned origin.depth.depth) afterDepth = .done origin.ordinary final
  pending : IsPending key final

/-- The actual Depth callback preserves the complete source context. -/
theorem Site.depthContext [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) : Context site.afterDepth site.names := by
  simpa only [site.depthDone, Outcome.state] using site.context.callback site.body .depth (depth_available site.before)

/-- Both current callbacks preserve the complete source context. -/
theorem Site.finalContext [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) : Context final site.names := by
  simpa only [site.ordinaryDone, Outcome.state] using
    site.depthContext.callback site.body (.uninterned origin.depth.depth) (ordinary_available site.afterDepth origin.depth.depth)

/-- The current probes finish after the active ancestor's original reservation cut. -/
theorem Site.growth [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) :
    Grows site.before site.afterDepth ∧ Grows site.afterDepth final ∧ Grows origin.cut final := by
  have depthGrowth : Grows site.before site.afterDepth := by
    simpa only [site.depthDone, Outcome.state] using
      (callback_growing site.body (site.names.map Value.reference) .depth site.before site.context.normal.facts.coherent.valid).2
  have ordinaryGrowth : Grows site.afterDepth final := by
    simpa only [site.ordinaryDone, Outcome.state] using
      (callback_growing site.body (site.names.map Value.reference) (.uninterned origin.depth.depth)
        site.afterDepth site.depthContext.normal.facts.coherent.valid).2
  have allocated : Grows origin.cut origin.allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  exact ⟨depthGrowth, ordinaryGrowth, grows_trans allocated (grows_trans site.initial (grows_trans depthGrowth ordinaryGrowth))⟩

/-- Closed execution identifies both current callback results with the actual original probe records. -/
theorem closed_site [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, Nonempty (Site origin final) := by
  obtain ⟨origin, smart, body, names, before, depth, afterDepth, ordinary, crossings,
    captures, context, path, initial, traces, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable, sameKey, waiting⟩ :=
    InternedPendingOrdinaryOrigins.closed_encounter expression key final pending
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
  exact ⟨origin, ⟨⟨smart, body, names, before, afterDepth, crossings, captures, context, path, initial, traces,
    by simpa only [depthSame] using depthDone,
    by simpa only [depthSame, ordinarySame] using ordinaryDone, waiting⟩⟩⟩

/-- Both completed probes recover every live capture, including either supplied sentinel. -/
theorem probes_capture [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (names : List Reference) (before afterDepth final : State Symbol Guard) (context : Context before names)
    (depth ordinary : Value Symbol Guard)
    (depthDone : callback body (names.map Value.reference) .depth before = .done depth afterDepth)
    (ordinaryDone : callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary final)
    (name : Reference) :
    name ∈ InternedFreeNameDecoder.decode .depth (.uninterned depth.depth) depth.free ordinary.free ↔
      name ∈ liveInputs (.binder smart body) names := by
  have depthContext : Context afterDepth names := by
    simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
  apply InternedFreeNameDecoder.decode_observed
    (liveInputs (.binder smart body) names) depth.free ordinary.free .depth (.uninterned depth.depth)
    (by intro impossible; cases impossible)
  · intro other different
    simpa using callback_other smart body names id .depth before afterDepth (by simpa using context)
      (depth_available before) depth (by simpa using depthDone) other different
  · intro other different
    simpa using callback_other smart body names id (.uninterned depth.depth) afterDepth final (by simpa using depthContext)
      (ordinary_available afterDepth depth.depth) ordinary (by simpa using ordinaryDone) other different

/-- Exact equality of both old probes forces equality of all live captured-name memberships. -/
theorem Site.capture_equivalent [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) (name : Reference) :
    name ∈ liveInputs (.binder site.smart site.body) site.names ↔
      name ∈ liveInputs (.binder origin.smart origin.body) origin.names := by
  have current := probes_capture site.smart site.body site.names site.before site.afterDepth final site.context
    origin.depth origin.ordinary site.depthDone site.ordinaryDone name
  have original := probes_capture origin.smart origin.body origin.names origin.before origin.afterDepth origin.cut
    origin.context origin.depth origin.ordinary origin.depthDone origin.ordinaryDone name
  exact current.symm.trans original

end MicroCFTA.InternedPendingJointKey
