import MicroCFTA.InternedNestedProvenance
import MicroCFTA.InternedPreparedSubstitution

/-!
# Derived flat union records for complete source executions

Every stored union contains no further union at its immediate member level.
This property follows from the actual flattening operation and canonical
readback. It holds at both completed and pending nested execution states.
-/
namespace MicroCFTA.InternedUnionNormalForm
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedTemplateProvenance InternedConstructionProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedRequestFacts InternedNestedProvenance
open InternedBinderProtocol (NodeKey Reference)

/-- A normalized union operand has no further union at its root. -/
def Atomic : Value Symbol Guard → Prop
  | .union .. => False
  | _ => True

/-- Immediate members of a stored union have already been flattened. -/
def FlatValue : Value Symbol Guard → Prop
  | .union _ members _ _ => ∀ member ∈ members, Atomic member
  | _ => True

/-- Every actual stored union is flat. -/
def Flat (state : State Symbol Guard) : Prop :=
  ∀ key value, state.nodeRecords key = some value → FlatValue value

/-- Empty source tables satisfy union normalization. -/
theorem empty_flat : Flat (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key value impossible
  cases impossible

/-- Available canonical records inherit union normalization from their table. -/
theorem resident_flat (state : State Symbol Guard) (flat : Flat state)
    (value : Value Symbol Guard) (resident : Resident state value) : FlatValue value := by
  cases value with
  | union entry members depth free => exact flat entry.key _ (resident entry rfl)
  | empty | reference | node | mu => trivial

/-- Flattening one normalized input emits only nonunion operands. -/
theorem flat_members (value : Value Symbol Guard) (flat : FlatValue value) :
    ∀ member ∈ unionMembers value, Atomic member := by
  cases value <;> simp_all [unionMembers, Atomic, FlatValue]

/-- A canonical node request retains an old normalized record or adds its normalized candidate. -/
theorem nodeStep_flat (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) (flat : Flat state) (candidate : ∀ entry, FlatValue (identify entry)) :
    Flat (nodeStep key identify state).2 := by
  intro other value present
  rcases record_cases _ key other _ value present with old | ⟨same, equal⟩
  · exact flat other value old
  · subst other value
    exact candidate _

/-- Ordinary source node construction cannot add a union record. -/
theorem makeNode_flat [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (flat : Flat state) : Flat (run (makeNode edges) state).2 := by
  unfold makeNode
  dsimp only
  split
  · exact flat
  · exact nodeStep_flat _ _ state flat (fun _ => trivial)

/-- Actual union construction establishes flat candidates from all normalized available inputs. -/
theorem makeUnion_flat [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (flat : Flat state) (available : Values state values) :
    Flat (run (makeUnion values) state).2 := by
  have atomic : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Atomic value := by
    intro value member
    obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact flat_members source (resident_flat state flat source (available source included).resident) value inner
  unfold makeUnion
  split
  · exact flat
  · exact flat
  · split
    · exact makeNode_flat _ state flat
    · simp only [run]
      exact nodeStep_flat _ _ state flat (fun _ => atomic)

/-- The actual root self filter preserves normalized union payloads. -/
theorem filter_flat [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (flat : Flat state) (available : Available state value) :
    Flat (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact flat
  case union entry members depth free =>
    split
    · exact makeUnion_flat _ state flat (fun value member => available.children value (List.mem_filter.mp member).1)
    · exact flat

/-- Completing a Mu adds no union payload of its own. -/
theorem complete_flat (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (flat : Flat state) :
    Flat (complete smart entry body depth ordinary state).state := by
  intro key value present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary) value present with old | ⟨same, equal⟩
  · exact flat key value old
  · subst key value
    trivial

/-- Sequencing supplies derived records and flatness at the exact intermediate source state. -/
theorem bind_flat (state : State Symbol Guard) (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (property : State Symbol Guard → First → Prop) (verified : Verified state outcome property)
    (flat : Flat outcome.state)
    (later : ∀ value after, outcome = .done value after → Facts after → property after value → Flat after → Flat (next value after).state) :
    Flat (outcome.bind next).state := by
  cases outcome with
  | pending => exact flat
  | done value after => exact later value after rfl verified.facts (verified.result value after rfl) flat

/-- Source binder reservation and readback preserve flat union records. -/
theorem request_flat [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (flat : Flat state)
    (checked : ∀ name current, Grows state current → Extends state.nodes.issued current.nodes.issued →
      Facts current → Available current (.reference name) → Flat current →
      Verified current (callback name current) Available ∧ Flat (callback name current).state) :
    Flat (request smart depth ordinary callback state).state := by
  unfold request
  dsimp only
  split
  · split <;> exact flat
  · let key := muKey depth ordinary
    let entry := Cache.intern state.nodes key
    let allocated := {state with nodes := entry.2}
    have growth : Grows state allocated :=
      ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
    have body := checked (.interned entry.1.identity) allocated growth
      (intern_issued_extends state.nodes key facts.coherent.valid.2) (reserve_facts key state facts)
      (reserve_available key state facts.coherent facts.cached).2 flat
    exact bind_flat allocated _ _ Available body.1 body.2
      (fun value after _ _ _ afterFlat => complete_flat smart entry.1 value depth ordinary after afterFlat)

mutual
/-- Complete source syntax establishes flat union records through every dynamic nested binder. -/
theorem build_flat [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (flat : Flat state) :
    Flat (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using flat
  | node edges =>
      rw [build]
      exact bind_flat state _ _ Edges (buildEdges_verified edges environment state facts inputs)
        (buildEdges_flat edges environment state facts inputs flat)
        (fun values after _ _ _ afterFlat => makeNode_flat values after afterFlat)
  | union members =>
      rw [build]
      exact bind_flat state _ _ Values (buildMany_verified members environment state facts inputs)
        (buildMany_flat members environment state facts inputs flat)
        (fun values after _ _ available afterFlat => makeUnion_flat values after afterFlat available)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have checked : ∀ name current, Facts current → Values current environment → Available current (.reference name) → Flat current →
          Verified current (callback name current) Available ∧ Flat (callback name current).state := by
        intro name current currentFacts currentInputs localAvailable currentFlat
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact localAvailable
          · exact currentInputs value present
        have verified := build_verified body (.reference name :: environment) current currentFacts withLocal
        exact ⟨bind_verified current _ _ Available Available verified
          (fun value after _ afterFacts available => filter_verified name value after afterFacts available),
          bind_flat current _ _ Available verified (build_flat body _ current currentFacts withLocal currentFlat)
            (fun value after _ _ available afterFlat => filter_flat name value after afterFlat available)⟩
      have depth := checked .depth state facts inputs (depth_available state) flat
      rw [build]
      change Flat ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      apply bind_flat state _ _ Available depth.1 depth.2
      intro depthValue afterDepth returned depthFacts _ depthFlat
      have depthInputs : Values afterDepth environment := by
        intro value member
        simpa [returned, Outcome.state] using depth.1.available value (inputs value member)
      have ordinary := checked (.uninterned depthValue.depth) afterDepth depthFacts depthInputs
        (ordinary_available afterDepth depthValue.depth) depthFlat
      apply bind_flat afterDepth _ _ Available ordinary.1 ordinary.2
      intro ordinaryValue afterOrdinary ordinaryReturned ordinaryFacts _ ordinaryFlat
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa [ordinaryReturned, Outcome.state] using ordinary.1.available value (depthInputs value member)
      apply request_flat smart depthValue ordinaryValue callback afterOrdinary ordinaryFacts ordinaryFlat
      intro name current growth history currentFacts localAvailable currentFlat
      exact checked name current currentFacts
        (fun value member => (finalInputs value member).grows afterOrdinary current growth history) localAvailable currentFlat
termination_by sizeOf expression

/-- Flat union records persist through the original ordered child schedule. -/
theorem buildMany_flat [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (flat : Flat state) :
    Flat (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using flat
  | cons first rest =>
      have head := build_verified first environment state facts inputs
      rw [buildMany]
      apply bind_flat state _ _ Available head (build_flat first environment state facts inputs flat)
      intro value afterHead returned headFacts _ headFlat
      have laterInputs : Values afterHead environment := by
        intro value member
        simpa [returned, Outcome.state] using head.available value (inputs value member)
      exact bind_flat afterHead _ _ Values (buildMany_verified rest environment afterHead headFacts laterInputs)
        (buildMany_flat rest environment afterHead headFacts laterInputs headFlat)
        (fun values afterTail _ _ _ tailFlat => tailFlat)
termination_by sizeOf expressions

/-- Edge effects preserve flat node records while their children run in source order. -/
theorem buildEdges_flat [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (flat : Flat state) :
    Flat (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using flat
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have childrenBuilt := buildMany_verified children environment state facts inputs
          rw [buildEdges]
          apply bind_flat state _ _ Values childrenBuilt (buildMany_flat children environment state facts inputs flat)
          intro values afterChildren childrenReturned childrenFacts valuesAvailable childrenFlat
          have edgeBuilt := edge_verified symbol constraint values afterChildren childrenFacts valuesAvailable
          apply bind_flat afterChildren _ _ InternedEdgeResidency.EdgeResident edgeBuilt childrenFlat
          intro edge afterEdge edgeReturned edgeFacts _ edgeFlat
          have laterInputs : Values afterEdge environment := by
            intro value member
            have intermediate : Available afterChildren value := by
              simpa [childrenReturned, Outcome.state] using childrenBuilt.available value (inputs value member)
            simpa [edgeReturned, Outcome.state] using edgeBuilt.available value intermediate
          exact bind_flat afterEdge _ _ Edges (buildEdges_verified rest environment afterEdge edgeFacts laterInputs)
            (buildEdges_flat rest environment afterEdge edgeFacts laterInputs edgeFlat)
            (fun edges afterTail _ _ _ tailFlat => tailFlat)
termination_by sizeOf expressions
end

/-- Empty-state source execution derives normalization without a final-shape premise. -/
theorem closed_flat [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Flat (build expression [] empty).state :=
  build_flat expression [] empty empty_facts (by intro value member; cases member) empty_flat

end MicroCFTA.InternedUnionNormalForm
