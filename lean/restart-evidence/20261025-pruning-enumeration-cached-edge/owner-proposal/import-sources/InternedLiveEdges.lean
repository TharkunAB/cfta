import MicroCFTA.InternedNestedRequestFacts

/-!
# Derived live-edge normalization for the complete source executor

Every stored ordinary edge lacks an EmptyNode child. The invariant follows
from makeNode normalization and survives all nested source constructor
branches, including pending outcomes. Arbitrary earlier inputs need no
separate liveness premise.
-/
namespace MicroCFTA.InternedLiveEdges
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency
open InternedNestedConstruction InternedNestedRequestFacts
open InternedBinderProtocol (NodeKey Reference)

/-- The actual outgoing edges of one ordinary record have no empty child. -/
def ValueLive (value : Value Symbol Guard) : Prop :=
  ∀ edge ∈ nodeEdges value, edge.children.any (fun child => child.referenceOf == .empty) = false

/-- Every stored ordinary record satisfies source empty-child normalization. -/
def Live (state : State Symbol Guard) : Prop :=
  ∀ key value, state.nodeRecords key = some value → ValueLive value

/-- Initial tables have no outgoing-edge obligations. -/
theorem empty_live : Live (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key value impossible
  cases impossible

/-- Actual resident records inherit normalization from the source table. -/
theorem resident_live (state : State Symbol Guard) (live : Live state)
    (value : Value Symbol Guard) (resident : Resident state value) : ValueLive value := by
  cases value with
  | empty | reference | mu | union => simp [ValueLive, nodeEdges]
  | node entry edges depth free => exact live entry.key _ (resident entry rfl)

/-- A node request installs a normalized candidate or retains a normalized earlier record. -/
theorem nodeStep_live (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) (live : Live state) (candidate : ∀ entry, ValueLive (identify entry)) :
    Live (nodeStep key identify state).2 := by
  intro other value present
  rcases record_cases _ key other _ value present with old | ⟨same, equal⟩
  · exact live other value old
  · subst other value
    exact candidate _

/-- Source edge allocation leaves the ordinary node payload table unchanged. -/
theorem makeEdge_live [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (live : Live state) :
    Live (run (makeEdge symbol constraint values) state).2 := live

/-- The source node constructor establishes normalization from its actual filter. -/
theorem makeNode_live [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (live : Live state) : Live (run (makeNode edges) state).2 := by
  have normalized : ∀ edge ∈ canonicalEdges (surviving edges),
      edge.children.any (fun child => child.referenceOf == .empty) = false := by
    intro edge member
    have selected := (List.mem_filter.mp (canonicalEdges_member _ edge member)).2
    simpa using selected
  unfold makeNode
  dsimp only
  split
  · exact live
  · rename_i first rest same
    apply nodeStep_live _ _ state live
    intro entry edge member
    exact normalized edge (by simpa only [same, identifyNode, nodeEdges] using member)

/-- All union branches preserve normalization. An ordinary merge reruns the source node filter. -/
theorem makeUnion_live [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (live : Live state) : Live (run (makeUnion values) state).2 := by
  unfold makeUnion
  split
  · exact live
  · exact live
  · split
    · exact makeNode_live _ state live
    · simp only [run]
      apply nodeStep_live _ _ state live
      intro entry edge impossible
      simp [nodeEdges] at impossible

/-- Removing a root self operand preserves the same stored normalization invariant. -/
theorem filter_live [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (live : Live state) :
    Live (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact live
  case union => split <;> first | exact makeUnion_live _ state live | exact live

/-- Completing a Mu adds no ordinary outgoing edge of its own. -/
theorem complete_live (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (live : Live state) :
    Live (complete smart entry body depth ordinary state).state := by
  intro key value present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary) value present with
    old | ⟨same, equal⟩
  · exact live key value old
  · subst key value
    intro edge impossible
    simp [nodeEdges] at impossible

/-- Sequential source effects retain the invariant at success or pending return. -/
theorem bind_live (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : Live outcome.state)
    (later : ∀ value state, outcome = .done value state → Live state → Live (next value state).state) :
    Live (outcome.bind next).state := by
  cases outcome with
  | pending => exact first
  | done value state => exact later value state rfl first

/-- Lookup, reservation, pending readback, and completion preserve live ordinary edges. -/
theorem request_live [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (live : Live state)
    (callbackLive : ∀ name current, Live current → Live (callback name current).state) :
    Live (request smart depth ordinary callback state).state := by
  unfold request
  dsimp only
  split
  · split <;> exact live
  · apply bind_live
    · exact callbackLive _ _ live
    · intro body after _ afterLive
      exact complete_live smart _ body depth ordinary after afterLive

mutual
/-- Every nested source expression preserves actual stored edge normalization. -/
theorem build_live [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (live : Live state) :
    Live (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using live
  | node edges =>
      rw [build]
      exact bind_live _ _ (buildEdges_live edges environment state live)
        (fun values after _ afterLive => makeNode_live values after afterLive)
  | union members =>
      rw [build]
      exact bind_live _ _ (buildMany_live members environment state live)
        (fun values after _ afterLive => makeUnion_live values after afterLive)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have checked : ∀ name current, Live current → Live (callback name current).state := by
        intro name current currentLive
        exact bind_live _ _ (build_live body _ current currentLive)
          (fun value after _ afterLive => filter_live name value after afterLive)
      rw [build]
      change Live ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      apply bind_live _ _ (checked .depth state live)
      intro depth afterDepth _ depthLive
      apply bind_live _ _ (checked (.uninterned depth.depth) afterDepth depthLive)
      intro ordinary afterOrdinary _ ordinaryLive
      exact request_live smart depth ordinary callback afterOrdinary ordinaryLive checked
termination_by sizeOf expression

/-- The exact source child order preserves normalization through every nested effect. -/
theorem buildMany_live [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (live : Live state) :
    Live (buildMany expression environment state).state := by
  cases expression with
  | nil => simpa only [buildMany, Outcome.state] using live
  | cons first rest =>
      rw [buildMany]
      apply bind_live _ _ (build_live first environment state live)
      intro value afterHead _ headLive
      exact bind_live _ _ (buildMany_live rest environment afterHead headLive)
        (fun values afterTail _ tailLive => tailLive)
termination_by sizeOf expression

/-- Edge construction cannot introduce a dead edge into an already stored node. -/
theorem buildEdges_live [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (live : Live state) :
    Live (buildEdges expression environment state).state := by
  cases expression with
  | nil => simpa only [buildEdges, Outcome.state] using live
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_live _ _ (buildMany_live children environment state live)
          intro values afterChildren _ childrenLive
          apply bind_live (work (makeEdge symbol constraint values) afterChildren) _
            (makeEdge_live symbol constraint values afterChildren childrenLive)
          intro edge afterEdge _ edgeLive
          exact bind_live _ _ (buildEdges_live rest environment afterEdge edgeLive)
            (fun edges afterTail _ tailLive => tailLive)
termination_by sizeOf expression
end

/-- Actual empty-cache nested executions establish the invariant without a liveness premise. -/
theorem closed_live [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Live (build expression [] empty).state := build_live expression [] empty empty_live

end MicroCFTA.InternedLiveEdges
