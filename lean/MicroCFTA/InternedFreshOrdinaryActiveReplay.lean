import MicroCFTA.InternedFreshOrdinaryActiveSite
import MicroCFTA.InternedFreshOrdinaryProbeChoiceSites

/-!
# Earlier completed representatives for repaired active source paths

The ancestor's actual raw Depth body completed before its reservation.
Its completed descendant route keeps ordinary choices and replaces fresh
choices with Depth. Captured lexical values remain unchanged.
-/
namespace MicroCFTA.InternedFreshOrdinaryActiveReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work work_correct)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryActiveOrigins
open InternedFreshOrdinaryActiveSite
open InternedBinderProtocol (Reference NodeKey)

/-- Ordinary entries select ordinary replay; Depth and fresh entries select Depth replay. -/
def Crossing.probeChoice [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard) : Bool :=
  match crossing.name with
  | .uninterned _ => true
  | _ => false

/-- The actual path fixes both the source body and the probe choice at every crossing. -/
theorem Path.probe_route [DecidableEq (EdgeKey Symbol Guard)] {expression target : Syntax Symbol Guard}
    {environment current : List (Value Symbol Guard)} {crossings : List (Crossing Symbol Guard)}
    (path : Path expression environment target current crossings) :
    InternedProbeChoiceSites.Route expression target (crossings.map (fun crossing => (crossing.body, Crossing.probeChoice crossing))) := by
  induction path with
  | here => exact .here _
  | node edge member nested ih => exact .node edge member ih
  | union member nested ih => exact .union member ih
  | binder crossing nested ih =>
      simpa only [List.map_append, List.map_cons, List.map_nil] using
        InternedProbeChoiceSites.Route.binder (Crossing.probeChoice crossing) ih

/-- Actual callback entries use only the two source sentinels or a reserved interned name. -/
theorem Crossing.name_cases [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard) :
    crossing.name = .depth ∨ (∃ level, crossing.name = .uninterned level) ∨ (∃ identity, crossing.name = .interned identity) := by
  rcases crossing with ⟨smart, body, environment, before, name, start, context, entered⟩
  cases entered with
  | depth => exact Or.inl rfl
  | ordinary depth _ _ => exact Or.inr (Or.inl ⟨(InternedFreshOrdinaryConstruction.ordinaryLevel depth), rfl⟩)
  | fresh depth ordinary _ cut _ _ _ => exact Or.inr (Or.inr ⟨(Cache.intern cut.nodes (muKey depth ordinary)).1.identity, rfl⟩)

/-- The active ancestor's raw Depth call completed before its reservation cut. -/
theorem Origin.rawDepth_before_cut [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) :
    Grows origin.afterRawDepth origin.cut := by
  have localContext := origin.context.local .depth (depth_available origin.before)
  have rawContext : Context origin.afterRawDepth (.reference .depth :: origin.environment) := by
    simpa only [List.map_cons, origin.rawDepthDone, Outcome.state] using localContext.build origin.body
  have filtered : work (withoutSelfReference .depth origin.rawDepth) origin.afterRawDepth = .done origin.depth origin.afterDepth := by
    simpa only [callback, origin.rawDepthDone, Outcome.bind] using origin.depthDone
  have filterGrowth : Grows origin.afterRawDepth origin.afterDepth := by
    simpa only [filtered, Outcome.state] using
      (work_correct (withoutSelfReference .depth origin.rawDepth) origin.afterRawDepth rawContext.normal.facts.coherent.valid).2
  have depthContext : Context origin.afterDepth origin.environment := by
    simpa only [origin.depthDone, Outcome.state] using origin.context.callback origin.body .depth (depth_available origin.before)
  have ordinaryGrowth : Grows origin.afterDepth origin.cut := by
    simpa only [origin.ordinaryDone, Outcome.state] using
      (callback_growing origin.body origin.environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel origin.depth))
        origin.afterDepth depthContext.normal.facts.coherent.valid).2
  exact grows_trans filterGrowth ordinaryGrowth

/-- Each actual active descendant has an earlier completed source representative with matching probe choices. -/
theorem Origin.completed_representative [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    {target : Syntax Symbol Guard} {environment : List (Value Symbol Guard)} {crossings : List (Crossing Symbol Guard)}
    (path : Path origin.body origin.localInputs target environment crossings) :
    ∃ earlier : List (InternedFreshOrdinaryProbeChoiceSites.Crossing Symbol Guard), ∃ start value finish,
      earlier.map (fun crossing => (crossing.body, crossing.ordinary)) =
        crossings.map (fun crossing => (crossing.body, Crossing.probeChoice crossing)) ∧
      build target (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment)
        start = .done value finish ∧
      Context start (earlier.map (fun crossing => Value.reference crossing.name) ++ .reference .depth :: origin.environment) ∧
      Grows origin.before start ∧ Grows finish origin.cut ∧
      ∀ crossing ∈ earlier, Grows origin.before crossing.before ∧ Grows crossing.afterDepth origin.cut := by
  obtain ⟨earlier, start, value, finish, choices, completed, context, initial, suffix, traces⟩ :=
    InternedFreshOrdinaryProbeChoiceSites.completed_route (Path.probe_route path) (.reference .depth :: origin.environment) origin.before origin.afterRawDepth origin.rawDepth
      (origin.context.local .depth (depth_available origin.before))
      (by simpa only [List.map_cons] using origin.rawDepthDone)
  exact ⟨earlier, start, value, finish, choices, completed, context, initial, grows_trans suffix (Origin.rawDepth_before_cut origin),
    fun crossing member => ⟨(traces crossing member).1, grows_trans (traces crossing member).2 (Origin.rawDepth_before_cut origin)⟩⟩

/-- Each fresh local on an active descendant path is at least as new as the active ancestor. -/
theorem Crossing.interned_after [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (crossing : Crossing Symbol Guard) (growth : Grows origin.allocated crossing.before)
    (identity : Nat) (same : crossing.name = .interned identity) : origin.cut.nodes.next ≤ identity := by
  have installed : origin.allocated.nodes.table key = some origin.entry :=
    (Cache.intern_correct origin.cut.nodes key origin.cutContext.normal.facts.coherent.valid.2).2.1
  have current := (grows_trans growth crossing.facts.2).nodes key origin.entry installed
  have valid := crossing.facts.1.normal.facts.coherent.valid.2
  have age := valid.1 origin.entry.identity key (valid.2 key origin.entry current).2
  have ancestor : origin.entry.identity = origin.cut.nodes.next :=
    InternedFreshProbeKeys.intern_miss_identity origin.cut.nodes key origin.missing
  rcases crossing with ⟨smart, body, environment, before, name, start, context, entered⟩
  cases entered with
  | depth => cases same
  | ordinary => cases same
  | fresh depth ordinary afterDepth cut depthDone ordinaryDone missing =>
      simp only [InternedFreshProbeKeys.intern_miss_identity cut.nodes _ missing, Reference.interned.injEq] at same
      have next : (Cache.intern cut.nodes (muKey depth ordinary)).2.next = cut.nodes.next + 1 := by
        simp [Cache.intern, missing, Cache.reserve, Cache.install]
      change origin.entry.identity < (Cache.intern cut.nodes (muKey depth ordinary)).2.next at age
      rw [ancestor, next] at age
      omega

/-- No fresh interned name from an actual crossed callback is a live capture at the pending site. -/
theorem Site.crossed_fresh_not_captured [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) (crossing : Crossing Symbol Guard)
    (member : crossing ∈ site.crossings) (identity : Nat) (same : crossing.name = .interned identity) :
    .interned identity ∉ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic site.body (site.environment.map InternedRootProfile.profile) (site.environment.map Value.free)) := by
  intro included
  have old := site.capture_below identity included
  have fresh := Crossing.interned_after origin crossing (site.traces crossing member).1 identity same
  omega

end MicroCFTA.InternedFreshOrdinaryActiveReplay
