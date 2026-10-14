import MicroCFTA.InternedFreshOrdinarySemanticOrigins
import MicroCFTA.InternedFreshOrdinaryPureProbeGate

/-!
# Joint probe opacity in actual repaired source construction

The original semantic context and both actual callback executions give the
same symbolic opacity. One pure Depth probe therefore suffices for completed
repaired unfolding and strict head-rank decrease. The ordinary name remains
the repaired fresh choice and need not have level zero.
-/
namespace MicroCFTA.InternedFreshOrdinaryProbeOpacity
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values depth_available)
open InternedRootProfile InternedProfileSemantics InternedProfileCallbackForm
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryPureProbeGate InternedGateRank
open InternedBinderProtocol (Reference NodeKey)

/-- Each completed repaired callback has the opacity of its one symbolic source execution. -/
theorem callback_opaque [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (context : Context state environment) (argument : Available state (.reference name))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (completed : callback expression environment name state = .done value after) :
    profile value = none ↔ symbolic expression (environment.map profile) = none := by
  have inputs := (context.local name argument).inputs
  have raw := InternedFreshOrdinaryProfiles.build_profile expression (.reference name :: environment) state
    context.normal inputs context.profiles
  have checked := InternedFreshOrdinaryProfileExecutionFacts.callback_checked expression environment name state
    context.normal inputs (by simpa only [List.map_cons, profile] using raw)
  have same := checked.result value after completed
  calc
    profile value = none ↔ normalize name (evaluate expression (some [name] :: environment.map profile)) = none := same.1
    _ ↔ evaluate expression (some [name] :: environment.map profile) = none := by
      cases evaluate expression (some [name] :: environment.map profile) <;> simp [normalize]
    _ ↔ symbolic expression (environment.map profile) = none := by
      rw [evaluate_supplied]
      cases symbolic expression (environment.map profile) <;> simp [mapNames]

/-- The exact original repaired probe calls have equal opacity, including captured sentinel aliases. -/
theorem origin_probes [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (origin : InternedFreshOrdinarySemanticOrigins.Origin entry body depth ordinary) :
    profile depth = none ↔ profile ordinary = none := by
  obtain ⟨expression, environment, before, afterDepth, afterOrdinary, _, context, depthDone, ordinaryDone, _⟩ := origin
  have afterContext : Context afterDepth environment := by
    simpa only [depthDone, Outcome.state] using context.callback expression .depth (depth_available before)
  exact (callback_opaque expression environment .depth before context (depth_available before) depth afterDepth depthDone).trans
    (callback_opaque expression environment (.uninterned (ordinaryLevel depth)) afterDepth afterContext
      (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth)) ordinary afterOrdinary ordinaryDone).symm

/-- Every actual stored repaired pair after empty-cache source execution is jointly pure or jointly opaque. -/
theorem closed_probes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    profile depth = none ↔ profile ordinary = none :=
  origin_probes entry body depth ordinary
    (InternedFreshOrdinarySemanticOrigins.closed_origins expression key entry body depth ordinary stored)

/-- One pure actual Depth probe derives completed repaired unfolding and a strict head-rank decrease. -/
theorem closed_depth_pure_unfold [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (names : List Reference) (pure : profile depth = some names)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
      (build expression [] empty).state = .done value final ∧
      headRank value < headRank (.mu entry body depth ordinary) := by
  cases ordinaryProfile : profile ordinary with
  | none =>
      have impossible := (closed_probes expression key entry body depth ordinary stored).mpr ordinaryProfile
      simp [pure] at impossible
  | some ordinaryNames =>
      exact closed_unfold_decreases expression key entry body depth ordinary stored names ordinaryNames pure ordinaryProfile opened

end MicroCFTA.InternedFreshOrdinaryProbeOpacity
