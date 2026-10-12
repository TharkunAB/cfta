import MicroCFTA.InternedNestedCoverage
import MicroCFTA.InternedNestedProvenance

/-!
# Actual reservation origins of possible pending readbacks

Each pending key originates at an actual missing lookup after two complete
available probes. Later effects preserve that reservation and both probe
records. The fresh name of that reservation is absent from both probes.
-/
namespace MicroCFTA.InternedPendingOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedCoverage InternedNestedRequestFacts
open InternedBinderProtocol (NodeKey Reference)

/-- A key's origin records its actual fresh reservation after complete available source probes. -/
def Origin (key : NodeKey) (current : State Symbol Guard) : Prop :=
  ∃ before depth ordinary, key = muKey depth ordinary ∧ before.nodes.table key = none ∧
    Coherent before ∧ Available before depth ∧ Available before ordinary ∧ Grows before current ∧
    current.nodes.table key = some (Cache.intern before.nodes key).1

/-- Every allowed pending key has its actual earlier source reservation and complete probe provenance. -/
def Origins (pending : List NodeKey) (current : State Symbol Guard) : Prop :=
  ∀ key ∈ pending, Origin key current

/-- Both successful and pending outcomes retain the exact reservation provenance that they need. -/
def Certified (pending : List NodeKey) (outcome : Outcome Symbol Guard Result) : Prop :=
  match outcome with
  | .done _ state => Origins pending state ∧ Covered pending state
  | .pending key state => Origin key state

/-- Later source effects preserve the actual reservation and its complete earlier probes. -/
theorem Origin.grows {key : NodeKey} {before after : State Symbol Guard} (origin : Origin key before)
    (growth : Grows before after) : Origin key after := by
  obtain ⟨original, depth, ordinary, same, missing, coherent, depthAvailable, ordinaryAvailable, earlier, stored⟩ := origin
  exact ⟨original, depth, ordinary, same, missing, coherent, depthAvailable, ordinaryAvailable,
    grows_trans earlier growth, growth.nodes key _ stored⟩

/-- An unchanged pending-key list retains each actual origin after constructor effects. -/
theorem Origins.grows {pending : List NodeKey} {before after : State Symbol Guard}
    (origins : Origins pending before) (growth : Grows before after) : Origins pending after :=
  fun key member => (origins key member).grows growth

/-- A source reservation adds its own derived origin and preserves all earlier origins. -/
theorem reserve_origins (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (missing : state.nodes.table (muKey depth ordinary) = none) (origins : Origins pending state) :
    Origins (muKey depth ordinary :: pending) {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} := by
  let key := muKey depth ordinary
  let allocated := {state with nodes := (Cache.intern state.nodes key).2}
  have growth : Grows state allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  intro selected member
  rcases List.mem_cons.mp member with rfl | previous
  · exact ⟨state, depth, ordinary, rfl, missing, facts.coherent, depthAvailable, ordinaryAvailable,
      growth, (Cache.intern_correct state.nodes key facts.coherent.valid.2).2.1⟩
  · exact (origins selected previous).grows growth

/-- Ordinary work preserves pending coverage and all earlier reservation origins. -/
theorem work_certified [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (origins : Origins pending state) (covered : Covered pending state) : Certified pending (work computation state) :=
  ⟨origins.grows (InternedConstructorTemplates.run_correct computation state valid).2,
    run_covered computation state valid covered⟩

/-- Source sequencing forwards complete provenance or propagates the exact existing pending origin. -/
theorem bind_certified (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (certified : Certified pending outcome) (verified : Verified before outcome property)
    (later : ∀ value state, outcome = .done value state → Facts state → property state value →
      Origins pending state → Covered pending state → Certified pending (next value state)) :
    Certified pending (outcome.bind next) := by
  cases outcome with
  | pending key state => exact certified
  | done value state => exact later value state rfl verified.facts (verified.result value state rfl) certified.1 certified.2

/-- Actual Mu lookup either reuses a complete record or exposes the origin of its exact pending key. -/
theorem request_certified [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (origins : Origins pending state) (covered : Covered pending state)
    (bodyCertified : ∀ name current, Grows state current → Extends state.nodes.issued current.nodes.issued →
      Facts current → Available current (.reference name) → Origins (muKey depth ordinary :: pending) current →
      Covered (muKey depth ordinary :: pending) current → Certified (muKey depth ordinary :: pending) (callback name current)) :
    Certified pending (request smart depth ordinary callback state) := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases found : state.nodeRecords (muKey depth ordinary) with
      | some value => simpa only [request, installed, found, Certified] using And.intro origins covered
      | none =>
          have waiting := covered.nodes _ entry installed
          rcases waiting with member | ⟨value, impossible⟩
          · simpa only [request, installed, found, Certified] using origins _ member
          · rw [found] at impossible
            cases impossible
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have growth : Grows state allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends state.nodes key facts.coherent.valid.2
      have body := bodyCertified (.interned entry.1.identity) allocated growth history (reserve_facts key state facts)
        (InternedConstructionProvenance.reserve_available key state facts.coherent facts.cached).2
        (reserve_origins depth ordinary state facts depthAvailable ordinaryAvailable installed origins)
        (reserve_covered key state covered)
      simp only [request, installed]
      change Certified pending ((callback (.interned entry.1.identity) allocated).bind
        (fun value after => complete smart entry.1 value depth ordinary after))
      cases returned : callback (.interned entry.1.identity) allocated with
      | pending selected after => simpa only [returned, Outcome.bind, Certified] using body
      | done value after =>
          rw [returned] at body
          simp only [Outcome.bind, complete, Certified]
          constructor
          · intro selected member
            exact (body.1 selected (List.mem_cons_of_mem _ member)).grows
              ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩
          · exact complete_covered smart entry.1 value depth ordinary after body.2 _ _ rfl

end MicroCFTA.InternedPendingOrigins
