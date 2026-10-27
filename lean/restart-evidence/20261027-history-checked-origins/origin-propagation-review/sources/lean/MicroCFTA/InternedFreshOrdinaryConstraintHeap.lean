import MicroCFTA.InternedFreshOrdinaryFacts

/-!
# Constraint invariants of actual repaired construction

Each edge request uses its original constraint. Node requests, body filters,
and Mu reservations do not change edge records. A predicate established by
input constraint constructors therefore remains true in the complete cache.
-/
namespace MicroCFTA.InternedFreshOrdinaryConstraintHeap
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedFreshOrdinaryConstruction

/-- Every stored edge key satisfies the source constraint invariant. -/
def Heap (property : Guard → Prop) (state : State Symbol Guard) : Prop :=
  ∀ key edge, state.edgeRecords key = some edge → property key.constraint

mutual
/-- Every original annotation in a lexical construction plan satisfies the invariant. -/
def SyntaxValid (property : Guard → Prop) : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesValid property edges
  | .union members => ManyValid property members
  | .binder _ body => SyntaxValid property body

/-- Ordered child plans satisfy the same annotation invariant. -/
def ManyValid (property : Guard → Prop) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => SyntaxValid property first ∧ ManyValid property rest

/-- Every edge annotation and its ordered child plans satisfy the invariant. -/
def EdgesValid (property : Guard → Prop) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ constraint children :: rest => property constraint ∧ ManyValid property children ∧ EdgesValid property rest
end

/-- The empty edge cache satisfies every constraint invariant. -/
theorem empty_heap (property : Guard → Prop) : Heap property (empty (Symbol := Symbol)) := by
  intro key edge impossible
  cases impossible

/-- A source edge request retains older annotations and installs its checked new annotation. -/
theorem edge_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (symbol : Symbol) (constraint : Guard) (children : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap property state) (checked : property constraint) :
    Heap property (run (makeEdge symbol constraint children) state).2 := by
  intro key edge present
  rcases record_cases state.edgeRecords ⟨symbol, children.map Value.referenceOf, constraint⟩ key
    (.mk (Cache.intern state.edges ⟨symbol, children.map Value.referenceOf, constraint⟩).1 children) edge present with old | ⟨same, _⟩
  · exact heap key edge old
  · exact same ▸ checked

/-- Ordinary node normalization does not change the edge cache. -/
theorem node_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (heap : Heap property state) :
    Heap property (run (makeNode edges) state).2 := by
  simp only [makeNode]
  split <;> exact heap

/-- Union normalization retains every stored edge constraint. -/
theorem union_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (heap : Heap property state) :
    Heap property (run (makeUnion values) state).2 := by
  unfold makeUnion
  split <;> first | exact heap | (split <;> first | exact heap | exact node_heap property _ state heap)

/-- Removing a bare self reference retains every edge annotation. -/
theorem filter_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (name : InternedBinderProtocol.Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap property state) :
    Heap property (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact heap
  split
  · exact union_heap property _ state heap
  · exact heap

/-- Sequential execution retains the invariant at its actual stopping cache. -/
theorem bind_heap (property : Guard → Prop) (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result) (heap : Heap property outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap property after → Heap property (next value after).state) :
    Heap property (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- Mu cache hits, pending entries, reservations, and completed callbacks retain edge constraints. -/
theorem request_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : InternedBinderProtocol.Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap property state)
    (checked : ∀ name current, Heap property current → Heap property (callback name current).state) :
    Heap property (request smart depth ordinary callback state).state := by
  simp only [request]
  split
  · split <;> exact heap
  · apply bind_heap property _ _ (checked _ {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} heap)
    intro body after done afterHeap
    exact afterHeap

mutual
/-- The actual repaired executor retains every checked original edge annotation. -/
theorem build_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap property state) (checked : SyntaxValid property expression) :
    Heap property (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using heap
  | node edges =>
      rw [build]
      apply bind_heap property _ _ (buildEdges_heap property edges environment state heap checked)
      intro values after done afterHeap
      exact node_heap property values after afterHeap
  | union members =>
      rw [build]
      apply bind_heap property _ _ (buildMany_heap property members environment state heap checked)
      intro values after done afterHeap
      exact union_heap property values after afterHeap
  | binder smart body =>
      have callback (name : InternedBinderProtocol.Reference) (current : State Symbol Guard) (currentHeap : Heap property current) :
          Heap property ((build body (.reference name :: environment) current).bind
            fun value next => work (withoutSelfReference name value) next).state := by
        apply bind_heap property _ _ (build_heap property body _ current currentHeap checked)
        intro value after done afterHeap
        exact filter_heap property name value after afterHeap
      rw [build]
      apply bind_heap property _ _ (callback _ state heap)
      intro depth afterDepth doneDepth depthHeap
      apply bind_heap property _ _ (callback _ afterDepth depthHeap)
      intro ordinary afterOrdinary doneOrdinary ordinaryHeap
      exact request_heap property smart depth ordinary _ afterOrdinary ordinaryHeap callback
termination_by sizeOf expression

/-- Actual sequential child construction retains every checked annotation. -/
theorem buildMany_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap property state) (checked : ManyValid property expressions) :
    Heap property (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using heap
  | cons first rest =>
      rw [buildMany]
      apply bind_heap property _ _ (build_heap property first environment state heap checked.1)
      intro value after done afterHeap
      apply bind_heap property _ _ (buildMany_heap property rest environment after afterHeap checked.2)
      intro values final returned finalHeap
      exact finalHeap
termination_by sizeOf expressions

/-- Actual edge allocation checks the original constraint after its children complete. -/
theorem buildEdges_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop)
    (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap property state) (checked : EdgesValid property expressions) :
    Heap property (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_heap property _ _ (buildMany_heap property children environment state heap checked.2.1)
          intro values after done afterHeap
          apply bind_heap property (work (makeEdge symbol constraint values) after) _
            (edge_heap property symbol constraint values after afterHeap checked.1)
          intro edge afterEdge returned edgeHeap
          apply bind_heap property _ _ (buildEdges_heap property rest environment afterEdge edgeHeap checked.2.2)
          intro edges final returned finalHeap
          exact finalHeap
termination_by sizeOf expressions
end

end MicroCFTA.InternedFreshOrdinaryConstraintHeap
