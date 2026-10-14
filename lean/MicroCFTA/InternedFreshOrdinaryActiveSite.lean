import MicroCFTA.InternedFreshOrdinaryActiveEncounter
import MicroCFTA.InternedFreeNameDecoder

/-!
# Both original repaired probes at the exact pending source site

The active ancestor, captured values, actual descendant path, and both
complete probe records remain in one witness. Canonical readback derives
both record equalities. No probe-equality or callback-replay contract is
supplied. The lexical prefix retains every actual crossed reference.
-/
namespace MicroCFTA.InternedFreshOrdinaryActiveSite
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome IsPending)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryContext InternedFreshOrdinaryActiveOrigins
open InternedBinderProtocol (Reference NodeKey)

/-- An actual pending site retains both original ancestor records and every actual source crossing. -/
structure Site [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) (final : State Symbol Guard) where
  smart : Bool
  body : Syntax Symbol Guard
  environment : List (Value Symbol Guard)
  before : State Symbol Guard
  afterDepth : State Symbol Guard
  crossings : List (Crossing Symbol Guard)
  context : Context before environment
  path : Path origin.body origin.localInputs (.binder smart body) environment crossings
  initial : Grows origin.allocated before
  traces : ∀ crossing ∈ crossings, Grows origin.allocated crossing.before ∧ Grows crossing.start before
  depthDone : InternedFreshOrdinaryFacts.callback body environment .depth before = .done origin.depth afterDepth
  ordinaryDone : InternedFreshOrdinaryFacts.callback body environment
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel origin.depth)) afterDepth = .done origin.ordinary final
  pending : IsPending key final

/-- The actual original Depth callback retains its complete semantic context. -/
theorem Site.depthContext [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) : Context site.afterDepth site.environment := by
  simpa only [site.depthDone, Outcome.state] using site.context.callback site.body .depth (depth_available site.before)

/-- The actual original ordinary callback retains its complete semantic context. -/
theorem Site.finalContext [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) : Context final site.environment := by
  simpa only [site.ordinaryDone, Outcome.state] using site.depthContext.callback site.body
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel origin.depth))
    (ordinary_available site.afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel origin.depth))

/-- An actual encounter retains the specified ancestor when canonical readback identifies both original probes. -/
theorem encounter_site_at [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) (final : State Symbol Guard)
    (encounter : InternedFreshOrdinaryActiveEncounter.AtOrigin origin final) : Nonempty (Site origin final) := by
  obtain ⟨smart, body, environment, before, depth, afterDepth, ordinary, crossings,
    context, path, initial, traces, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable, sameKey, pending⟩ := encounter
  have depthContext : Context afterDepth environment := by
    simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
  have finalContext : Context final environment := by
    simpa only [ordinaryDone, Outcome.state] using depthContext.callback body
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
      (ordinary_available afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
  have depthGrowth : Grows before afterDepth := by
    simpa only [depthDone, Outcome.state] using (callback_growing body environment .depth before context.normal.facts.coherent.valid).2
  have ordinaryGrowth : Grows afterDepth final := by
    simpa only [ordinaryDone, Outcome.state] using (callback_growing body environment
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthContext.normal.facts.coherent.valid).2
  obtain ⟨sameDepth, sameOrdinary⟩ := origin.probes_eq final finalContext.normal.facts.coherent
    (grows_trans initial (grows_trans depthGrowth ordinaryGrowth)) depth ordinary depthAvailable ordinaryAvailable sameKey
  subst depth
  subst ordinary
  exact ⟨⟨smart, body, environment, before, afterDepth, crossings, context, path, initial, traces, depthDone, ordinaryDone, pending⟩⟩

/-- An actual pending encounter derives one site with both exact original ancestor records. -/
theorem encounter_site [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (final : State Symbol Guard)
    (encounter : InternedFreshOrdinaryActiveEncounter.Encounter key final) :
    ∃ origin : Origin Symbol Guard key, Nonempty (Site origin final) := by
  obtain ⟨origin, atOrigin⟩ := encounter
  exact ⟨origin, encounter_site_at origin final atOrigin⟩

/-- Every actual site retains its crossed references before the unchanged captured values. -/
theorem Site.inputs [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) :
    site.environment = site.crossings.map (fun crossing => Value.reference crossing.name) ++ origin.localInputs := site.path.inputs

/-- Both repaired probes recover every captured free name in arbitrary lexical values. -/
theorem probes_capture [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before afterDepth final : State Symbol Guard)
    (context : Context before environment) (depth ordinary : Value Symbol Guard)
    (depthDone : InternedFreshOrdinaryFacts.callback body environment .depth before = .done depth afterDepth)
    (ordinaryDone : InternedFreshOrdinaryFacts.callback body environment
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth = .done ordinary final)
    (name : Reference) :
    name ∈ InternedFreeNameDecoder.decode .depth
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) depth.free ordinary.free ↔
    name ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (environment.map InternedRootProfile.profile) (environment.map Value.free)) := by
  have depthContext : Context afterDepth environment := by
    simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
  apply InternedFreeNameDecoder.decode_observed
    (InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (environment.map InternedRootProfile.profile) (environment.map Value.free)))
    depth.free ordinary.free .depth (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
    (by intro impossible; cases impossible)
  · intro other different
    exact InternedFreshOrdinarySourceFreeNames.callback_other body environment .depth before context.normal
      (context.local .depth (depth_available before)).inputs context.freeNames context.profiles
      depth afterDepth depthDone other different
  · intro other different
    exact InternedFreshOrdinarySourceFreeNames.callback_other body environment
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthContext.normal
      (depthContext.local _ (ordinary_available afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel depth))).inputs
      depthContext.freeNames depthContext.profiles ordinary final ordinaryDone other different

/-- Exact original probe records force equality of all captured free-name memberships. -/
theorem Site.capture_equivalent [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) (name : Reference) :
    name ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic site.body (site.environment.map InternedRootProfile.profile) (site.environment.map Value.free)) ↔
    name ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic origin.body (origin.environment.map InternedRootProfile.profile) (origin.environment.map Value.free)) := by
  have current := probes_capture site.body site.environment site.before site.afterDepth final site.context
    origin.depth origin.ordinary site.depthDone site.ordinaryDone name
  have original := probes_capture origin.body origin.environment origin.before origin.afterDepth origin.cut origin.context
    origin.depth origin.ordinary origin.depthDone origin.ordinaryDone name
  exact current.symm.trans original

/-- Every live interned capture at the pending site predates the ancestor reservation. -/
theorem Site.capture_below [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) (identity : Nat)
    (member : .interned identity ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic site.body (site.environment.map InternedRootProfile.profile) (site.environment.map Value.free))) :
    identity < origin.cut.nodes.next := by
  have original := (site.capture_equivalent (.interned identity)).mp member
  have decoded := (probes_capture origin.body origin.environment origin.before origin.afterDepth origin.cut origin.context
    origin.depth origin.ordinary origin.depthDone origin.ordinaryDone (.interned identity)).mpr original
  simp only [InternedFreeNameDecoder.decode, List.mem_append, List.mem_filter] at decoded
  rcases decoded with ⟨included, _⟩ | ⟨included, _⟩
  · exact InternedFreshProbeKeys.issued_free_below origin.cut.nodes origin.cutContext.normal.facts.coherent.valid.2
      origin.depth origin.depthAvailable.issued identity included
  · exact InternedFreshProbeKeys.issued_free_below origin.cut.nodes origin.cutContext.normal.facts.coherent.valid.2
      origin.ordinary origin.ordinaryAvailable.issued identity included

/-- The active ancestor's fresh name cannot be a live capture at the exact pending site. -/
theorem Site.fresh_not_captured [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) :
    .interned origin.entry.identity ∉ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic site.body (site.environment.map InternedRootProfile.profile) (site.environment.map Value.free)) := by
  intro included
  have below := site.capture_below origin.entry.identity included
  have fresh : origin.entry.identity = origin.cut.nodes.next :=
    InternedFreshProbeKeys.intern_miss_identity origin.cut.nodes key origin.missing
  exact Nat.lt_irrefl _ (fresh ▸ below)

end MicroCFTA.InternedFreshOrdinaryActiveSite
