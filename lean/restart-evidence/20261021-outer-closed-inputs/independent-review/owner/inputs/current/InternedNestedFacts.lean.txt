import MicroCFTA.InternedNestedConstructionGrowth
import MicroCFTA.InternedEdgeResidency

/-!
# Record invariants for nested constructor outcomes

Completed and pending outcomes retain canonical record coherence, complete
child provenance, and outgoing edge residency. Reservation history makes
earlier inputs available after later nested effects.
-/
namespace MicroCFTA.InternedNestedFacts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedConstructionProvenance InternedEdgeResidency
open InternedNestedConstruction
open InternedBinderProtocol (Reference NodeKey)

/-- The three source record invariants used by nested construction. -/
structure Facts (state : State Symbol Guard) : Prop where
  coherent : Coherent state
  cached : Cached state
  linked : Linked state

/-- The source starts with all record invariants established. -/
theorem empty_facts : Facts (empty (Symbol := Symbol) (Guard := Guard)) :=
  ⟨empty_correct.1, empty_cached, empty_linked⟩

/-- Both outcomes preserve actual state histories. A completed result also
has the local record property required by its caller. -/
structure Verified (before : State Symbol Guard) (outcome : Outcome Symbol Guard Result)
    (property : State Symbol Guard → Result → Prop) : Prop where
  facts : Facts outcome.state
  growth : Grows before outcome.state
  history : Extends before.nodes.issued outcome.state.nodes.issued
  result : ∀ value state, outcome = .done value state → property state value

/-- Every earlier available input remains available at the exact outcome state. -/
theorem Verified.available {before : State Symbol Guard} {outcome : Outcome Symbol Guard Result}
    {property : State Symbol Guard → Result → Prop}
    (verified : Verified before outcome property) (value : Value Symbol Guard)
    (available : Available before value) : Available outcome.state value :=
  available.grows before outcome.state verified.growth verified.history

/-- Returning an existing value requires no state effect. -/
theorem pure_verified (state : State Symbol Guard) (facts : Facts state) (value : Result)
    (property : State Symbol Guard → Result → Prop) (valid : property state value) :
    Verified state (.done value state) property := by
  refine ⟨facts, grows_refl _, extends_refl _, ?_⟩
  intro found after same
  cases same
  exact valid

/-- A pending readback preserves its exact current state. -/
theorem pending_verified (state : State Symbol Guard) (facts : Facts state) (key : NodeKey)
    (property : State Symbol Guard → Result → Prop) : Verified state (.pending key state) property := by
  refine ⟨facts, grows_refl _, extends_refl _, ?_⟩
  intro value after impossible
  cases impossible

/-- Source sequencing composes both histories and passes only a completed
value's derived local property to the next constructor. -/
theorem bind_verified (before : State Symbol Guard) (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstProperty : State Symbol Guard → First → Prop)
    (resultProperty : State Symbol Guard → Result → Prop)
    (first : Verified before outcome firstProperty)
    (later : ∀ value state, outcome = .done value state → Facts state → firstProperty state value →
      Verified state (next value state) resultProperty) :
    Verified before (outcome.bind next) resultProperty := by
  cases outcome with
  | pending key state =>
      exact ⟨first.facts, first.growth, first.history, by intro value after impossible; cases impossible⟩
  | done value state =>
      have second := later value state rfl first.facts (first.result value state rfl)
      exact ⟨second.facts, grows_trans first.growth second.growth,
        extends_trans first.history second.history, second.result⟩

/-- Any ordinary work step uses its actual growth and issued-reference history. -/
theorem work_verified [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (state : State Symbol Guard) (before : Facts state)
    (property : State Symbol Guard → Result → Prop)
    (after : Facts (run computation state).2) (result : property (run computation state).2 (run computation state).1) :
    Verified state (work computation state) property := by
  refine ⟨after, (InternedConstructorTemplates.run_correct computation state before.coherent.valid).2,
    run_issued_extends computation state before.coherent.valid, ?_⟩
  intro value later same
  cases same
  exact result

/-- Actual edge readback establishes canonical edge residency. Its children
retain availability through the existing complete-record invariant. -/
theorem edge_verified [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : ∀ value ∈ values, Available state value) :
    Verified state (work (makeEdge symbol constraint values) state) EdgeResident := by
  have built := makeEdge_available symbol constraint values state facts.coherent facts.cached available
  have links := makeEdge_linked symbol constraint values state facts.coherent facts.linked
  exact work_verified _ state facts _ ⟨built.1, built.2.1, links.1⟩ links.2

/-- Actual ordinary-node readback derives availability from resident source edges. -/
theorem node_verified [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    Verified state (work (makeNode edges) state) Available := by
  have children : ∀ child ∈ edges.flatMap EdgeValue.children, Available state child := by
    intro child member
    obtain ⟨edge, present, included⟩ := List.mem_flatMap.mp member
    exact facts.cached.edges edge.entry.key edge (resident edge present) child included
  have built := makeNode_available edges state facts.coherent facts.cached children
  exact work_verified _ state facts _
    ⟨built.1, built.2.1, makeNode_linked edges state facts.linked resident⟩ built.2.2

/-- Source union reconstruction establishes all record invariants from its actual operands. -/
theorem union_verified [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (available : ∀ value ∈ values, Available state value) :
    Verified state (work (makeUnion values) state) Available := by
  have built := makeUnion_available values state facts.coherent facts.cached available
  exact work_verified _ state facts _
    ⟨built.1, built.2.1, makeUnion_linked values state facts.linked available⟩ built.2.2

/-- The current root self-reference filter retains the same complete source invariants. -/
theorem filter_verified [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state value) :
    Verified state (work (withoutSelfReference name value) state) Available := by
  have built := InternedTemplateProvenance.withoutSelfReference_available name value state facts.coherent facts.cached available
  exact work_verified _ state facts _
    ⟨built.1, built.2.1, withoutSelfReference_linked name value state facts.linked available⟩ built.2.2

/-- Allocation preserves coherent old payloads without a completed-coverage assumption. -/
theorem reserve_facts (key : NodeKey) (state : State Symbol Guard) (facts : Facts state) :
    Facts {state with nodes := (Cache.intern state.nodes key).2} := by
  let allocated := {state with nodes := (Cache.intern state.nodes key).2}
  have growth : Grows state allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have coherent : Coherent allocated := by
    refine ⟨⟨facts.coherent.valid.1, (Cache.intern_correct state.nodes key facts.coherent.valid.2).1⟩,
      facts.coherent.edges, ?_⟩
    intro other value stored
    obtain ⟨entry, present, fields⟩ := facts.coherent.nodes other value stored
    exact ⟨entry, growth.nodes other entry present, fields⟩
  exact ⟨coherent, (reserve_available key state facts.coherent facts.cached).1, facts.linked⟩

/-- Raw and smart return paths retain an available record after cleanup. -/
theorem finish_available (smart : Bool) (value : Value Symbol Guard)
    (available : Available state value) : Available state (finish smart value) := by
  cases smart
  · exact available
  · exact cleanup_available value available

end MicroCFTA.InternedNestedFacts
