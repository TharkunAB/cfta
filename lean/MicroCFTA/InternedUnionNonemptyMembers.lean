import MicroCFTA.InternedNestedProvenance

/-!
# Nonempty members in every actual stored union

Source union normalization removes EmptyNode operands. This property is
preserved through complete canonical readback, root self filtering, and
arbitrary nested source execution, including pending outcomes.
-/
namespace MicroCFTA.InternedUnionNonemptyMembers
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedTemplateProvenance InternedConstructionProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedRequestFacts InternedNestedProvenance
open InternedBinderProtocol (NodeKey Reference)

/-- A retained source union member is not EmptyNode. -/
def MemberNonempty (value : Value Symbol Guard) : Prop := value.referenceOf ≠ .empty

/-- Every immediate member of a stored union is nonempty. -/
def ValueMembers : Value Symbol Guard → Prop
  | .union _ members _ _ => ∀ member ∈ members, MemberNonempty member
  | _ => True

/-- Every stored union excludes EmptyNode members. -/
def MembersNonempty (state : State Symbol Guard) : Prop :=
  ∀ key value, state.nodeRecords key = some value → ValueMembers value

/-- Empty source tables satisfy union normalization. -/
theorem empty_membersNonempty : MembersNonempty (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key value impossible
  cases impossible

/-- Available canonical records inherit union normalization from their table. -/
theorem resident_membersNonempty (state : State Symbol Guard) (membersNonempty : MembersNonempty state)
    (value : Value Symbol Guard) (resident : Resident state value) : ValueMembers value := by
  cases value with
  | union entry members depth free => exact membersNonempty entry.key _ (resident entry rfl)
  | empty | reference | node | mu => trivial

/-- Flattening one normalized input emits only nonempty operands. -/
theorem membersNonempty_members (value : Value Symbol Guard) (membersNonempty : ValueMembers value) :
    ∀ member ∈ unionMembers value, MemberNonempty member := by
  cases value <;> simp_all [unionMembers, MemberNonempty, Value.referenceOf, ValueMembers]

/-- A canonical node request retains an old normalized record or adds its normalized candidate. -/
theorem nodeStep_membersNonempty (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) (membersNonempty : MembersNonempty state) (candidate : ∀ entry, ValueMembers (identify entry)) :
    MembersNonempty (nodeStep key identify state).2 := by
  intro other value present
  rcases record_cases _ key other _ value present with old | ⟨same, equal⟩
  · exact membersNonempty other value old
  · subst other value
    exact candidate _

/-- Ordinary source node construction cannot add a union record. -/
theorem makeNode_membersNonempty [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (membersNonempty : MembersNonempty state) : MembersNonempty (run (makeNode edges) state).2 := by
  unfold makeNode
  dsimp only
  split
  · exact membersNonempty
  · exact nodeStep_membersNonempty _ _ state membersNonempty (fun _ => trivial)

/-- Actual union construction establishes nonempty union members from all normalized available inputs. -/
theorem makeUnion_membersNonempty [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (membersNonempty : MembersNonempty state) (available : Values state values) :
    MembersNonempty (run (makeUnion values) state).2 := by
  have atomic : ∀ value ∈ distinctNodes (values.flatMap unionMembers), MemberNonempty value := by
    intro value member
    obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact membersNonempty_members source (resident_membersNonempty state membersNonempty source (available source included).resident) value inner
  unfold makeUnion
  split
  · exact membersNonempty
  · exact membersNonempty
  · split
    · exact makeNode_membersNonempty _ state membersNonempty
    · simp only [run]
      exact nodeStep_membersNonempty _ _ state membersNonempty (fun _ => atomic)

/-- The actual root self filter preserves normalized union payloads. -/
theorem filter_membersNonempty [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (membersNonempty : MembersNonempty state) (available : Available state value) :
    MembersNonempty (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact membersNonempty
  case union entry members depth free =>
    split
    · exact makeUnion_membersNonempty _ state membersNonempty (fun value member => available.children value (List.mem_filter.mp member).1)
    · exact membersNonempty

/-- Completing a Mu adds no union payload of its own. -/
theorem complete_membersNonempty (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (membersNonempty : MembersNonempty state) :
    MembersNonempty (complete smart entry body depth ordinary state).state := by
  intro key value present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary) value present with old | ⟨same, equal⟩
  · exact membersNonempty key value old
  · subst key value
    trivial

/-- Sequencing supplies derived records and membersNonemptyness at the exact intermediate source state. -/
theorem bind_membersNonempty (state : State Symbol Guard) (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (property : State Symbol Guard → First → Prop) (verified : Verified state outcome property)
    (membersNonempty : MembersNonempty outcome.state)
    (later : ∀ value after, outcome = .done value after → Facts after → property after value → MembersNonempty after → MembersNonempty (next value after).state) :
    MembersNonempty (outcome.bind next).state := by
  cases outcome with
  | pending => exact membersNonempty
  | done value after => exact later value after rfl verified.facts (verified.result value after rfl) membersNonempty

/-- Source binder reservation and readback preserve nonempty union members. -/
theorem request_membersNonempty [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (membersNonempty : MembersNonempty state)
    (checked : ∀ name current, Grows state current → Extends state.nodes.issued current.nodes.issued →
      Facts current → Available current (.reference name) → MembersNonempty current →
      Verified current (callback name current) Available ∧ MembersNonempty (callback name current).state) :
    MembersNonempty (request smart depth ordinary callback state).state := by
  unfold request
  dsimp only
  split
  · split <;> exact membersNonempty
  · let key := muKey depth ordinary
    let entry := Cache.intern state.nodes key
    let allocated := {state with nodes := entry.2}
    have growth : Grows state allocated :=
      ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
    have body := checked (.interned entry.1.identity) allocated growth
      (intern_issued_extends state.nodes key facts.coherent.valid.2) (reserve_facts key state facts)
      (reserve_available key state facts.coherent facts.cached).2 membersNonempty
    exact bind_membersNonempty allocated _ _ Available body.1 body.2
      (fun value after _ _ _ afterMembersNonempty => complete_membersNonempty smart entry.1 value depth ordinary after afterMembersNonempty)

mutual
/-- Complete source syntax establishes nonempty union members through every dynamic nested binder. -/
theorem build_membersNonempty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (membersNonempty : MembersNonempty state) :
    MembersNonempty (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using membersNonempty
  | node edges =>
      rw [build]
      exact bind_membersNonempty state _ _ Edges (buildEdges_verified edges environment state facts inputs)
        (buildEdges_membersNonempty edges environment state facts inputs membersNonempty)
        (fun values after _ _ _ afterMembersNonempty => makeNode_membersNonempty values after afterMembersNonempty)
  | union members =>
      rw [build]
      exact bind_membersNonempty state _ _ Values (buildMany_verified members environment state facts inputs)
        (buildMany_membersNonempty members environment state facts inputs membersNonempty)
        (fun values after _ _ available afterMembersNonempty => makeUnion_membersNonempty values after afterMembersNonempty available)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have checked : ∀ name current, Facts current → Values current environment → Available current (.reference name) → MembersNonempty current →
          Verified current (callback name current) Available ∧ MembersNonempty (callback name current).state := by
        intro name current currentFacts currentInputs localAvailable currentMembersNonempty
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact localAvailable
          · exact currentInputs value present
        have verified := build_verified body (.reference name :: environment) current currentFacts withLocal
        exact ⟨bind_verified current _ _ Available Available verified
          (fun value after _ afterFacts available => filter_verified name value after afterFacts available),
          bind_membersNonempty current _ _ Available verified (build_membersNonempty body _ current currentFacts withLocal currentMembersNonempty)
            (fun value after _ _ available afterMembersNonempty => filter_membersNonempty name value after afterMembersNonempty available)⟩
      have depth := checked .depth state facts inputs (depth_available state) membersNonempty
      rw [build]
      change MembersNonempty ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      apply bind_membersNonempty state _ _ Available depth.1 depth.2
      intro depthValue afterDepth returned depthFacts _ depthMembersNonempty
      have depthInputs : Values afterDepth environment := by
        intro value member
        simpa [returned, Outcome.state] using depth.1.available value (inputs value member)
      have ordinary := checked (.uninterned depthValue.depth) afterDepth depthFacts depthInputs
        (ordinary_available afterDepth depthValue.depth) depthMembersNonempty
      apply bind_membersNonempty afterDepth _ _ Available ordinary.1 ordinary.2
      intro ordinaryValue afterOrdinary ordinaryReturned ordinaryFacts _ ordinaryMembersNonempty
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa [ordinaryReturned, Outcome.state] using ordinary.1.available value (depthInputs value member)
      apply request_membersNonempty smart depthValue ordinaryValue callback afterOrdinary ordinaryFacts ordinaryMembersNonempty
      intro name current growth history currentFacts localAvailable currentMembersNonempty
      exact checked name current currentFacts
        (fun value member => (finalInputs value member).grows afterOrdinary current growth history) localAvailable currentMembersNonempty
termination_by sizeOf expression

/-- Nonempty union members persist through the original ordered child schedule. -/
theorem buildMany_membersNonempty [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (membersNonempty : MembersNonempty state) :
    MembersNonempty (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using membersNonempty
  | cons first rest =>
      have head := build_verified first environment state facts inputs
      rw [buildMany]
      apply bind_membersNonempty state _ _ Available head (build_membersNonempty first environment state facts inputs membersNonempty)
      intro value afterHead returned headFacts _ headMembersNonempty
      have laterInputs : Values afterHead environment := by
        intro value member
        simpa [returned, Outcome.state] using head.available value (inputs value member)
      exact bind_membersNonempty afterHead _ _ Values (buildMany_verified rest environment afterHead headFacts laterInputs)
        (buildMany_membersNonempty rest environment afterHead headFacts laterInputs headMembersNonempty)
        (fun values afterTail _ _ _ tailMembersNonempty => tailMembersNonempty)
termination_by sizeOf expressions

/-- Edge effects preserve nonempty union members while their children run in source order. -/
theorem buildEdges_membersNonempty [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (membersNonempty : MembersNonempty state) :
    MembersNonempty (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using membersNonempty
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have childrenBuilt := buildMany_verified children environment state facts inputs
          rw [buildEdges]
          apply bind_membersNonempty state _ _ Values childrenBuilt (buildMany_membersNonempty children environment state facts inputs membersNonempty)
          intro values afterChildren childrenReturned childrenFacts valuesAvailable childrenMembersNonempty
          have edgeBuilt := edge_verified symbol constraint values afterChildren childrenFacts valuesAvailable
          apply bind_membersNonempty afterChildren _ _ InternedEdgeResidency.EdgeResident edgeBuilt childrenMembersNonempty
          intro edge afterEdge edgeReturned edgeFacts _ edgeMembersNonempty
          have laterInputs : Values afterEdge environment := by
            intro value member
            have intermediate : Available afterChildren value := by
              simpa [childrenReturned, Outcome.state] using childrenBuilt.available value (inputs value member)
            simpa [edgeReturned, Outcome.state] using edgeBuilt.available value intermediate
          exact bind_membersNonempty afterEdge _ _ Edges (buildEdges_verified rest environment afterEdge edgeFacts laterInputs)
            (buildEdges_membersNonempty rest environment afterEdge edgeFacts laterInputs edgeMembersNonempty)
            (fun edges afterTail _ _ _ tailMembersNonempty => tailMembersNonempty)
termination_by sizeOf expressions
end

/-- Empty-state source execution derives normalization without a final-shape premise. -/
theorem closed_membersNonempty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    MembersNonempty (build expression [] empty).state :=
  build_membersNonempty expression [] empty empty_facts (by intro value member; cases member) empty_membersNonempty

end MicroCFTA.InternedUnionNonemptyMembers
