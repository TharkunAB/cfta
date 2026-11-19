import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.InternedStoredSubstitution

namespace MicroCFTA.InternedFreshOrdinaryNoUnionRecords
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedFreshProbeKeys InternedConstructionProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedFacts InternedNestedProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
variable {Symbol Guard A B : Type}
set_option autoImplicit false

/-- No complete constructor record has the union tag. -/
def NoUnionRecords (state : State Symbol Guard) : Prop :=
  ∀ key actual members level free,
    state.nodeRecords key ≠ some (.union actual members level free)

mutual
/-- Stored reconstruction uses no explicit union instruction. -/
def UnionFree : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => UnionFreeEdges edges
  | .union _ => False
  | .binder _ body => UnionFree body
termination_by expression => sizeOf expression

/-- Every ordered child instruction excludes explicit unions. -/
def UnionFreeMany : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => UnionFree first ∧ UnionFreeMany rest
termination_by expressions => sizeOf expressions

/-- Every edge child instruction excludes explicit unions. -/
def UnionFreeEdges : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => UnionFreeMany children ∧ UnionFreeEdges rest
termination_by expressions => sizeOf expressions
end

private theorem bind_no_union (outcome : Outcome Symbol Guard A)
    (next : A → State Symbol Guard → Outcome Symbol Guard B)
    (first : NoUnionRecords outcome.state)
    (later : ∀ value after, outcome = .done value after →
      NoUnionRecords after → NoUnionRecords (next value after).state) :
    NoUnionRecords (outcome.bind next).state
 := by
  cases outcome with
  | pending key after => exact first
  | done value after => exact later value after rfl first

private theorem makeNode_no_union [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (noUnion : NoUnionRecords state) :
    NoUnionRecords (run (makeNode edges) state).2
 := by
  have step (key : NodeKey) (rows : List (EdgeValue Symbol Guard)) :
      NoUnionRecords (nodeStep key (identifyNode rows) state).2 := by
    intro other actual members level free stored
    simp only [nodeStep] at stored
    change keepFirst state.nodeRecords key
      (identifyNode rows (Cache.intern state.nodes key).1) other =
        some (.union actual members level free) at stored
    rcases record_cases state.nodeRecords key other
      (identifyNode rows (Cache.intern state.nodes key).1)
      (.union actual members level free) stored with earlier | ⟨_, impossible⟩
    · exact noUnion other actual members level free earlier
    · cases impossible
  unfold makeNode
  dsimp only
  split
  · exact noUnion
  · exact step _ _

private theorem makeEdge_no_union [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (constraint : Guard) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (noUnion : NoUnionRecords state) :
    NoUnionRecords (run (makeEdge symbol constraint values) state).2
 := by
  change NoUnionRecords state
  exact noUnion

private theorem filter_no_union [DecidableEq (EdgeKey Symbol Guard)]
    (name : Reference) (value : Value Symbol Guard) (state : State Symbol Guard)
    (noUnion : NoUnionRecords state) (available : Available state value) :
    NoUnionRecords (work (withoutSelfReference name value) state).state
 := by
  cases value with
  | union entry members level free =>
      exact False.elim (noUnion entry.key entry members level free
        (available.resident entry rfl))
  | empty | reference | node | mu =>
      simpa only [withoutSelfReference, work, run, Outcome.state] using noUnion

private theorem complete_no_union (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (noUnion : NoUnionRecords state) :
    NoUnionRecords (InternedNestedRequestFacts.complete smart entry body depth ordinary state).state
 := by
  intro key actual members level free present
  change keepFirst state.nodeRecords (muKey depth ordinary)
    (.mu entry body depth ordinary) key = some (.union actual members level free) at present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key
    (.mu entry body depth ordinary) (.union actual members level free) present with
    earlier | ⟨_, impossible⟩
  · exact noUnion key actual members level free earlier
  · cases impossible

private theorem request_no_union [DecidableEq (EdgeKey Symbol Guard)]
    (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (noUnion : NoUnionRecords state)
    (callbackNoUnion : ∀ name current, Grows state current →
      Extends state.nodes.issued current.nodes.issued → Facts current →
      Available current (.reference name) → NoUnionRecords current →
      NoUnionRecords (callback name current).state) :
    NoUnionRecords (request smart depth ordinary callback state).state
 := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases found : state.nodeRecords (muKey depth ordinary) with
      | none => simpa only [request, installed, found, Outcome.state] using noUnion
      | some value => simpa only [request, installed, found, Outcome.state] using noUnion
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated : State Symbol Guard := {state with nodes := entry.2}
      have growth : Grows state allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends state.nodes key facts.coherent.valid.2
      have allocatedNoUnion : NoUnionRecords allocated := noUnion
      have called := callbackNoUnion (.interned entry.1.identity) allocated growth history
        (reserve_facts key state facts)
        (reserve_available key state facts.coherent facts.cached).2 allocatedNoUnion
      simp only [request, installed]
      change NoUnionRecords ((callback (.interned entry.1.identity) allocated).bind
        (fun body after => InternedNestedRequestFacts.complete smart entry.1 body depth ordinary after)).state
      apply bind_no_union _ _ called
      intro body after returned afterNoUnion
      exact complete_no_union smart entry.1 body depth ordinary after afterNoUnion

mutual
theorem build_no_union [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (restricted : UnionFree expression) (noUnion : NoUnionRecords state) :
    NoUnionRecords (build expression environment state).state
 := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using noUnion
  | union members =>
      simp only [UnionFree] at restricted
  | node edges =>
      simp only [UnionFree] at restricted
      rw [build]
      apply bind_no_union _ _
        (buildEdges_no_union edges environment state facts inputs restricted noUnion)
      intro values after returned afterNoUnion
      simpa only [work, Outcome.state] using makeNode_no_union values after afterNoUnion
  | binder smart body =>
      simp only [UnionFree] at restricted
      have bodyRestricted : UnionFree body := restricted
      let callback := fun name current =>
        (build body (.reference name :: environment) current).bind
          fun value next => work (withoutSelfReference name value) next
      have checked : ∀ name current, Facts current → Values current environment →
          Available current (.reference name) → Verified current (callback name current) Available := by
        intro name current currentFacts currentInputs localAvailable
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact localAvailable
          · exact currentInputs value present
        exact bind_verified current _ _ Available Available
          (InternedFreshOrdinaryFacts.build_verified body (.reference name :: environment) current currentFacts withLocal)
          (fun value after _ afterFacts available => filter_verified name value after afterFacts available)
      have preserves : ∀ name current, Facts current → Values current environment →
          Available current (.reference name) → NoUnionRecords current →
          NoUnionRecords (callback name current).state := by
        intro name current currentFacts currentInputs localAvailable currentNoUnion
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact localAvailable
          · exact currentInputs value present
        have built := InternedFreshOrdinaryFacts.build_verified body (.reference name :: environment) current currentFacts withLocal
        apply bind_no_union _ _
          (build_no_union body (.reference name :: environment) current currentFacts withLocal
            bodyRestricted currentNoUnion)
        intro value after returned afterNoUnion
        exact filter_no_union name value after afterNoUnion (built.result value after returned)
      have depthChecked := checked .depth state facts inputs (depth_available state)
      have depthNoUnion := preserves .depth state facts inputs (depth_available state) noUnion
      rw [build]
      change NoUnionRecords ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      apply bind_no_union _ _ depthNoUnion
      intro depth afterDepth depthReturned afterDepthNoUnion
      have depthFacts : Facts afterDepth := by
        simpa only [depthReturned, Outcome.state] using depthChecked.facts
      have afterDepthInputs : Values afterDepth environment := by
        intro value member
        simpa only [depthReturned, Outcome.state] using depthChecked.available value (inputs value member)
      have ordinaryChecked := checked (.uninterned (ordinaryLevel depth)) afterDepth depthFacts
        afterDepthInputs (ordinary_available afterDepth (ordinaryLevel depth))
      have ordinaryNoUnion := preserves (.uninterned (ordinaryLevel depth)) afterDepth depthFacts
        afterDepthInputs (ordinary_available afterDepth (ordinaryLevel depth)) afterDepthNoUnion
      apply bind_no_union _ _ ordinaryNoUnion
      intro ordinary afterOrdinary ordinaryReturned afterOrdinaryNoUnion
      have ordinaryFacts : Facts afterOrdinary := by
        simpa only [ordinaryReturned, Outcome.state] using ordinaryChecked.facts
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa only [ordinaryReturned, Outcome.state] using
          ordinaryChecked.available value (afterDepthInputs value member)
      apply request_no_union smart depth ordinary callback afterOrdinary ordinaryFacts afterOrdinaryNoUnion
      intro name current growth history currentFacts localAvailable currentNoUnion
      exact preserves name current currentFacts
        (fun value member => (finalInputs value member).grows afterOrdinary current growth history)
        localAvailable currentNoUnion
termination_by sizeOf expression

theorem buildMany_no_union [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (restricted : UnionFreeMany expressions) (noUnion : NoUnionRecords state) :
    NoUnionRecords (buildMany expressions environment state).state
 := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using noUnion
  | cons first rest =>
      simp only [UnionFreeMany] at restricted
      have head := InternedFreshOrdinaryFacts.build_verified first environment state facts inputs
      rw [buildMany]
      apply bind_no_union _ _
        (build_no_union first environment state facts inputs restricted.1 noUnion)
      intro value after returned afterNoUnion
      have afterFacts : Facts after := by
        simpa only [returned, Outcome.state] using head.facts
      have afterInputs : Values after environment := by
        intro original member
        simpa only [returned, Outcome.state] using head.available original (inputs original member)
      apply bind_no_union _ _
        (buildMany_no_union rest environment after afterFacts afterInputs restricted.2 afterNoUnion)
      intro values final tailReturned finalNoUnion
      exact finalNoUnion
termination_by sizeOf expressions

theorem buildEdges_no_union [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (restricted : UnionFreeEdges expressions) (noUnion : NoUnionRecords state) :
    NoUnionRecords (buildEdges expressions environment state).state
 := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using noUnion
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [UnionFreeEdges] at restricted
          have childrenBuilt := InternedFreshOrdinaryFacts.buildMany_verified children environment state facts inputs
          rw [buildEdges]
          apply bind_no_union _ _
            (buildMany_no_union children environment state facts inputs restricted.1 noUnion)
          intro values afterChildren childrenReturned afterChildrenNoUnion
          have childrenFacts : Facts afterChildren := by
            simpa only [childrenReturned, Outcome.state] using childrenBuilt.facts
          have valuesAvailable := childrenBuilt.result values afterChildren childrenReturned
          have edgeBuilt := edge_verified symbol constraint values afterChildren childrenFacts valuesAvailable
          have edgeNoUnion : NoUnionRecords (work (makeEdge symbol constraint values) afterChildren).state := by
            simpa only [work, Outcome.state] using
              makeEdge_no_union symbol constraint values afterChildren afterChildrenNoUnion
          apply bind_no_union _ _ edgeNoUnion
          intro edge afterEdge edgeReturned afterEdgeNoUnion
          have edgeFacts : Facts afterEdge := by
            simpa only [edgeReturned, Outcome.state] using edgeBuilt.facts
          have tailInputs : Values afterEdge environment := by
            intro value member
            have intermediate : Available afterChildren value := by
              simpa only [childrenReturned, Outcome.state] using
                childrenBuilt.available value (inputs value member)
            simpa only [edgeReturned, Outcome.state] using edgeBuilt.available value intermediate
          apply bind_no_union _ _
            (buildEdges_no_union rest environment afterEdge edgeFacts tailInputs restricted.2 afterEdgeNoUnion)
          intro edges final tailReturned finalNoUnion
          exact finalNoUnion
termination_by sizeOf expressions

end

end MicroCFTA.InternedFreshOrdinaryNoUnionRecords

namespace MicroCFTA.InternedFreshOrdinaryStoredNoUnionRecords
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment encode encodeMany encodeEdges leaves input)
open InternedFreshOrdinaryNoUnionRecords
open InternedBinderProtocol (Reference)
set_option autoImplicit false
variable {Symbol Guard : Type}

mutual
private theorem encode_union_free
    (context : List (Value Symbol Guard)) (locals : List Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (available : Available state value) (inventory : NoUnionRecords state) :
    UnionFree (encode context locals value)
 := by
  rw [encode.eq_def]
  split
  · simp only [UnionFree]
  · cases value with
    | empty => simp only [UnionFree]
    | reference name =>
        dsimp only
        cases found : locals.findIdx? (fun candidate => candidate == name) <;>
          simp only [UnionFree]
    | node entry edges depth free =>
        change UnionFree (.node (encodeEdges context locals edges))
        simp only [UnionFree]
        exact encodeEdges_union_free context locals edges state
          (fun child member => available.children child member) inventory
    | union entry members depth free =>
        exact False.elim (inventory entry.key entry members depth free
          (available.resident entry rfl))
    | mu entry body depth ordinary =>
        change UnionFree (.binder true (encode context (.interned entry.identity :: locals) body))
        simp only [UnionFree]
        exact encode_union_free context (.interned entry.identity :: locals) body state
          (available.children body (by simp [InternedProbeProvenance.children])) inventory
termination_by sizeOf value

private theorem encodeMany_union_free
    (context : List (Value Symbol Guard)) (locals : List Reference)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (available : Values state values) (inventory : NoUnionRecords state) :
    UnionFreeMany (encodeMany context locals values)
 := by
  cases values with
  | nil => simp only [encodeMany, UnionFreeMany]
  | cons first rest =>
      simp only [encodeMany, UnionFreeMany]
      exact ⟨encode_union_free context locals first state
          (available first (by simp)) inventory,
        encodeMany_union_free context locals rest state
          (fun child member => available child (by simp [member])) inventory⟩
termination_by sizeOf values

private theorem encodeEdges_union_free
    (context : List (Value Symbol Guard)) (locals : List Reference)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (available : ∀ child ∈ edges.flatMap EdgeValue.children, Available state child)
    (inventory : NoUnionRecords state) :
    UnionFreeEdges (encodeEdges context locals edges)
 := by
  cases edges with
  | nil => simp only [encodeEdges, UnionFreeEdges]
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [encodeEdges, UnionFreeEdges]
          exact ⟨encodeMany_union_free context locals children state
              (fun child member => available child (by simp [EdgeValue.children, member]))
              inventory,
            encodeEdges_union_free context locals rest state
              (fun child member => available child (by simp [EdgeValue.children, member]))
              inventory⟩
termination_by sizeOf edges

end

theorem execute_no_union [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state)
    (available : Available state value)
    (replacements : InternedStoredSubstitution.Replacements state environment)
    (inventory : NoUnionRecords state) :
    NoUnionRecords (InternedFreshOrdinaryStoredSubstitution.execute
      value environment state).state
 := by
  exact build_no_union (encode (leaves value) [] value)
    ((leaves value).map (input environment)) state facts
    (InternedStoredSubstitution.inputs_available value environment state available replacements)
    (encode_union_free (leaves value) [] value state available inventory) inventory

end MicroCFTA.InternedFreshOrdinaryStoredNoUnionRecords

