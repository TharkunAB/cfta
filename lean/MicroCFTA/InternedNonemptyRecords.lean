import MicroCFTA.InternedNestedProvenance

/-!
# Source records have nonempty constructor shapes

Each stored ordinary node has an outgoing edge. Each stored union has at
least two members with distinct references. The actual constructors establish these conditions on
both completed and pending states of arbitrary nested source execution.
-/
namespace MicroCFTA.InternedNonemptyRecords
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys
open InternedNestedConstruction InternedNestedFacts InternedNestedRequestFacts InternedNestedProvenance
open InternedBinderProtocol (NodeKey Reference)

/-- Stored ordinary nodes have edges. Stored unions have at least two distinct member references. -/
def StoredNonempty : Value Symbol Guard → Prop
  | .node _ edges _ _ => edges ≠ []
  | .union _ members _ _ => 2 ≤ members.length ∧ (members.map Value.referenceOf).Nodup
  | _ => True

/-- Every actual complete payload has the constructor shape required by source normalization. -/
def NonemptyRecords (state : State Symbol Guard) : Prop :=
  ∀ key value, state.nodeRecords key = some value → StoredNonempty value

/-- Empty source tables contain no malformed constructor record. -/
theorem empty_nonempty : NonemptyRecords (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key value impossible
  cases impossible

/-- Actual canonical records inherit the constructor shape of their complete stored payload. -/
theorem resident_nonempty (state : State Symbol Guard) (nonempty : NonemptyRecords state)
    (value : Value Symbol Guard) (resident : Resident state value) : StoredNonempty value := by
  cases value with
  | node entry edges depth free => exact nonempty entry.key _ (resident entry rfl)
  | union entry members depth free => exact nonempty entry.key _ (resident entry rfl)
  | empty | reference | mu => trivial

/-- Canonical readback retains an old proper record or adds the specified proper candidate. -/
theorem nodeStep_nonempty (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) (nonempty : NonemptyRecords state) (candidate : ∀ entry, StoredNonempty (identify entry)) :
    NonemptyRecords (nodeStep key identify state).2 := by
  intro other value present
  rcases record_cases _ key other _ value present with old | ⟨same, equal⟩
  · exact nonempty other value old
  · subst other value
    exact candidate _

/-- Source ordinary node construction stores a candidate only after selecting a nonempty edge list. -/
theorem makeNode_nonempty [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (nonempty : NonemptyRecords state) : NonemptyRecords (run (makeNode edges) state).2 := by
  unfold makeNode
  dsimp only
  split
  · exact nonempty
  · apply nodeStep_nonempty _ _ state nonempty
    intro entry
    simp [StoredNonempty, identifyNode]

/-- Source first-identity deduplication emits distinct canonical references. -/
theorem distinctNodes_nodup (values : List (Value Symbol Guard)) :
    ((distinctNodes values).map Value.referenceOf).Nodup := by
  cases values with
  | nil => simp [distinctNodes]
  | cons first rest =>
      rw [distinctNodes, List.map_cons, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨value, selected, same⟩ := List.mem_map.mp member
        have original := distinctNodes_member _ value selected
        have different := (List.mem_filter.mp original).2
        simp [same] at different
      · exact distinctNodes_nodup (rest.filter (fun value => value.referenceOf != first.referenceOf))
termination_by values.length
decreasing_by
  have bound := List.length_filter_le (fun value => value.referenceOf != first.referenceOf) rest
  simp_wf
  omega

/-- Only the source branch with at least two operands stores a union record. -/
theorem makeUnion_nonempty [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (nonempty : NonemptyRecords state) :
    NonemptyRecords (run (makeUnion values) state).2 := by
  have distinct := distinctNodes_nodup (values.flatMap unionMembers)
  unfold makeUnion
  split
  · exact nonempty
  · exact nonempty
  · split
    · exact makeNode_nonempty _ state nonempty
    · simp only [run]
      apply nodeStep_nonempty _ _ state nonempty
      intro entry
      simp only [StoredNonempty]
      refine ⟨?_, distinct⟩
      cases selected : distinctNodes (values.flatMap unionMembers) with
      | nil => simp_all
      | cons first rest => cases rest <;> simp_all

/-- Root self-reference filtering preserves proper stored constructor shapes. -/
theorem filter_nonempty [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (nonempty : NonemptyRecords state) :
    NonemptyRecords (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact nonempty
  case union entry members depth free =>
    split
    · exact makeUnion_nonempty _ state nonempty
    · exact nonempty

/-- Completing a Mu introduces neither an empty ordinary node nor a small union. -/
theorem complete_nonempty (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (nonempty : NonemptyRecords state) :
    NonemptyRecords (complete smart entry body depth ordinary state).state := by
  intro key value present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary) value present with old | ⟨same, equal⟩
  · exact nonempty key value old
  · subst key value
    trivial

/-- Source sequencing preserves the constructor shape at each actual intermediate state. -/
theorem bind_nonempty (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (nonempty : NonemptyRecords outcome.state)
    (later : ∀ value after, outcome = .done value after → NonemptyRecords after → NonemptyRecords (next value after).state) :
    NonemptyRecords (outcome.bind next).state := by
  cases outcome with
  | pending => exact nonempty
  | done value after => exact later value after rfl nonempty

/-- Actual Mu reservation changes no stored payload, and completion adds only a Mu record. -/
theorem request_nonempty [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (nonempty : NonemptyRecords state)
    (checked : ∀ name current, NonemptyRecords current → NonemptyRecords (callback name current).state) :
    NonemptyRecords (request smart depth ordinary callback state).state := by
  unfold request
  dsimp only
  split
  · split <;> exact nonempty
  · let key := muKey depth ordinary
    let entry := Cache.intern state.nodes key
    let allocated := {state with nodes := entry.2}
    have body := checked (.interned entry.1.identity) allocated nonempty
    exact bind_nonempty _ _ body
      (fun value after _ afterNonempty => complete_nonempty smart entry.1 value depth ordinary after afterNonempty)

mutual
/-- Arbitrary source execution preserves proper record shapes on both completed and pending outcomes. -/
theorem build_nonempty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (nonempty : NonemptyRecords state) : NonemptyRecords (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using nonempty
  | node edges =>
      rw [build]
      exact bind_nonempty _ _ (buildEdges_nonempty edges environment state nonempty)
        (fun values after _ afterNonempty => makeNode_nonempty values after afterNonempty)
  | union members =>
      rw [build]
      exact bind_nonempty _ _ (buildMany_nonempty members environment state nonempty)
        (fun values after _ afterNonempty => makeUnion_nonempty values after afterNonempty)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have checked : ∀ name current, NonemptyRecords current → NonemptyRecords (callback name current).state := by
        intro name current currentNonempty
        exact bind_nonempty _ _ (build_nonempty body (.reference name :: environment) current currentNonempty)
          (fun value after _ afterNonempty => filter_nonempty name value after afterNonempty)
      rw [build]
      change NonemptyRecords ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      apply bind_nonempty _ _ (checked .depth state nonempty)
      intro depthValue afterDepth _ depthNonempty
      apply bind_nonempty _ _ (checked (.uninterned depthValue.depth) afterDepth depthNonempty)
      intro ordinaryValue afterOrdinary _ ordinaryNonempty
      exact request_nonempty smart depthValue ordinaryValue callback afterOrdinary ordinaryNonempty checked
termination_by sizeOf expression

/-- The source ordered child schedule preserves proper stored constructor shapes. -/
theorem buildMany_nonempty [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (nonempty : NonemptyRecords state) : NonemptyRecords (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using nonempty
  | cons first rest =>
      rw [buildMany]
      apply bind_nonempty _ _ (build_nonempty first environment state nonempty)
      intro value afterHead _ headNonempty
      exact bind_nonempty _ _ (buildMany_nonempty rest environment afterHead headNonempty)
        (fun values afterTail _ tailNonempty => tailNonempty)
termination_by sizeOf expressions

/-- Edge allocation changes no node record after its ordered child effects. -/
theorem buildEdges_nonempty [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (nonempty : NonemptyRecords state) : NonemptyRecords (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using nonempty
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_nonempty _ _ (buildMany_nonempty children environment state nonempty)
          intro values afterChildren _ childrenNonempty
          apply bind_nonempty (work (makeEdge symbol constraint values) afterChildren) _ childrenNonempty
          intro edge afterEdge _ edgeNonempty
          exact bind_nonempty _ _ (buildEdges_nonempty rest environment afterEdge edgeNonempty)
            (fun edges afterTail _ tailNonempty => tailNonempty)
termination_by sizeOf expressions
end

/-- A stored normalized union contains at least one nonempty member reference. -/
theorem union_has_nonempty (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth free)
    (proper : StoredNonempty (.union entry members depth free)) :
    ∃ value ∈ members, value.referenceOf ≠ .empty := by
  cases members with
  | nil => simp [StoredNonempty] at proper
  | cons first rest =>
      cases rest with
      | nil => simp [StoredNonempty] at proper
      | cons second tail =>
          have absent := (List.nodup_cons.mp proper.2).1
          by_cases nonempty : first.referenceOf = .empty
          · refine ⟨second, by simp, ?_⟩
            intro same
            apply absent
            simp [nonempty, same]
          · exact ⟨first, by simp, nonempty⟩

/-- Every arbitrary nested source execution from empty caches derives both stored cardinality bounds. -/
theorem closed_nonempty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    NonemptyRecords (build expression [] empty).state :=
  build_nonempty expression [] empty empty_nonempty

end MicroCFTA.InternedNonemptyRecords
