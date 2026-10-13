import MicroCFTA.InternedStoredProbeTags
import MicroCFTA.InternedPureProbeGate

/-!
# The two actual source probes have the same opacity

The full syntax map law makes callback opacity independent of the supplied
reference name. The original verified source calls transfer this fact to
every stored Mu. One pure depth probe therefore suffices for actual shallow
unfolding. The remaining gate rank case has two opaque probes.
-/
namespace MicroCFTA.InternedProbeOpacity
open Cache InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedNestedFacts InternedNestedProvenance InternedProbeProvenance InternedStoredMuOrigins
open InternedRootProfile InternedProfileSemantics InternedProfileCallbackForm InternedSourceProbeTags
open InternedProfileMuOrigins InternedPureProbeGate InternedGateRank
open InternedBinderProtocol (Reference NodeKey)

/-- Root filtering does not change profile opacity. -/
theorem normalize_none (name : Reference) (value : Profile) : normalize name value = none ↔ value = none := by
  cases value <;> simp [normalize]

/-- Each completed actual source callback has the opacity of its one symbolic execution. -/
theorem callback_opaque [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state (.reference name :: environment))
    (heap : InternedProfileHeap.Heap state) (value : Value Symbol Guard) (after : State Symbol Guard)
    (completed : callback expression environment name state = .done value after) :
    profile value = none ↔ symbolic expression (environment.map profile) = none := by
  have same := (callback_profile expression environment name state normal inputs heap).result value after completed
  calc
    profile value = none ↔ normalize name (evaluate expression (some [name] :: environment.map profile)) = none := same.1
    _ ↔ evaluate expression (some [name] :: environment.map profile) = none := normalize_none name _
    _ ↔ symbolic expression (environment.map profile) = none := by
      rw [evaluate_supplied]
      cases symbolic expression (environment.map profile) <;> simp [mapNames]

/-- The two original complete probe calls have the same opacity, including captured sentinel aliases. -/
theorem origin_probes [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (origin : InternedProfileMuOrigins.Origin entry body depth ordinary) :
    profile depth = none ↔ profile ordinary = none := by
  obtain ⟨expression, environment, before, afterDepth, afterOrdinary, _, normal, inputs, heap,
    depthDone, ordinaryDone, _⟩ := origin
  have depthInputs : Values before (.reference .depth :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact depth_available before
    · exact inputs value member
  have checked := callback_profile expression environment .depth before normal depthInputs heap
  have verified := callback_verified expression environment .depth before normal.facts depthInputs
  have afterNormal : Normal afterDepth := by
    simpa only [depthDone, Outcome.state] using callback_normal expression environment .depth before normal depthInputs
  have afterHeap : InternedProfileHeap.Heap afterDepth := by simpa only [depthDone, Outcome.state] using checked.heap
  have ordinaryInputs : Values afterDepth (.reference (.uninterned depth.depth) :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ordinary_available afterDepth depth.depth
    · simpa only [depthDone, Outcome.state] using verified.available value (inputs value member)
  exact (callback_opaque expression environment .depth before normal depthInputs heap depth afterDepth depthDone).trans
    (callback_opaque expression environment (.uninterned depth.depth) afterDepth afterNormal ordinaryInputs afterHeap
      ordinary afterOrdinary ordinaryDone).symm

/-- Every actual stored probe pair after arbitrary closed source execution is jointly pure or jointly opaque. -/
theorem closed_probes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    profile depth = none ↔ profile ordinary = none :=
  origin_probes entry body depth ordinary (closed_origins expression key entry body depth ordinary stored)

/-- A pure actual depth probe selects exactly the ordinary source sentinel at level zero. -/
theorem closed_pure_level [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (names : List Reference) (pure : profile depth = some names) : depth.depth = 0 := by
  have normal := build_normal expression [] empty empty_normal (by simp [Values])
  have available := normal.facts.cached.nodes key (.mu entry body depth ordinary) stored
  exact pure_depth_zero depth _ normal.facts.coherent (available.children depth (by simp [children])) names pure

/-- One pure canonical depth probe derives actual open-binder unfolding completion and strict rank decrease. -/
theorem closed_depth_pure_unfold [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (names : List Reference) (pure : profile depth = some names)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedStoredSubstitution.unfold (.mu entry body depth ordinary) (build expression [] empty).state = .done value final ∧
      headRank value < headRank (.mu entry body depth ordinary) := by
  cases ordinaryProfile : profile ordinary with
  | none =>
      have impossible := (closed_probes expression key entry body depth ordinary stored).mpr ordinaryProfile
      simp [pure] at impossible
  | some ordinaryNames =>
      exact closed_unfold_decreases expression key entry body depth ordinary stored names ordinaryNames pure ordinaryProfile opened

end MicroCFTA.InternedProbeOpacity
