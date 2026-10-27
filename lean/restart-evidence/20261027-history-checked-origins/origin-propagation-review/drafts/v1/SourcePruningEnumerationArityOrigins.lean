import MicroCFTA.InternedFreshOrdinaryConstraintHeap
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.SourcePruningEnumerationOwnArity

/-!
# Projected arity from actual checked construction

The invariant relates each stored edge key to its child count.
Checked source syntax supplies the initial facts.
Stored substitution retains the guard and the number of child plans.
These results do not change the raw constructor or its admission.
-/
namespace MicroCFTA.SourcePruningEnumerationArityOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open EnumerationState EnumerationCorrectness
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedFreshOrdinaryConstruction
open InternedStoredSubstitution (Environment encode encodeMany encodeEdges)
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Symbol : Type}

/-- A successful constraint projection names only existing root children. -/
def Fits (constraint : Constraint) (arity : Nat) : Prop :=
  ∀ tries residual,
    SourcePruningEnumerationConstraint.project constraint = some (tries, residual) →
    ∀ start, arityAllows arity (suspendedVars start tries) = true

/-- Every stored canonical edge key retains projected arity for its actual child count. -/
def Heap (state : State Symbol Constraint) : Prop :=
  ∀ key edge, state.edgeRecords key = some edge → Fits key.constraint key.children.length

/-- Coherent resident payloads have the child count stored in their canonical key. -/
theorem Heap.edge (state : State Symbol Constraint) (heap : Heap state)
    (coherent : Coherent state) (edge : EdgeValue Symbol Constraint)
    (resident : EdgeResident state edge) :
    Fits edge.entry.key.constraint edge.children.length := by
  have fields := (coherent.edges edge.entry.key edge resident).2.2
  have lengthSame : edge.children.length = edge.entry.key.children.length := by
    simpa only [List.length_map] using congrArg List.length fields
  have checked := heap edge.entry.key edge resident
  rw [← lengthSame] at checked
  exact checked

mutual
/-- Each source edge passes the projection check at its syntactic child count. -/
def Checked : Syntax Symbol Constraint → Prop
  | .empty | .var _ => True
  | .node edges => EdgesChecked edges
  | .union members => ManyChecked members
  | .binder _ body => Checked body

/-- Every ordered child plan has checked source edges. -/
def ManyChecked : List (Syntax Symbol Constraint) → Prop
  | [] => True
  | first :: rest => Checked first ∧ ManyChecked rest

/-- Checked source edges retain their own arity and all nested checks. -/
def EdgesChecked : List (EdgeSyntax Symbol Constraint) → Prop
  | [] => True
  | .mk _ constraint children :: rest =>
      Fits constraint children.length ∧ ManyChecked children ∧ EdgesChecked rest
end

/-- The empty edge-record table satisfies projected arity. -/
theorem empty_heap : Heap (empty (Symbol := Symbol) (Guard := Constraint)) := by
  intro key edge impossible
  cases impossible

/-- An actual edge request retains old records and checks the exact new key. -/
theorem edge_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (symbol : Symbol) (constraint : Constraint) (children : List (Value Symbol Constraint))
    (state : State Symbol Constraint) (heap : Heap state)
    (checked : Fits constraint children.length) :
    Heap (run (makeEdge symbol constraint children) state).2 := by
  intro key edge present
  rcases record_cases state.edgeRecords ⟨symbol, children.map Value.referenceOf, constraint⟩ key
    (.mk (Cache.intern state.edges ⟨symbol, children.map Value.referenceOf, constraint⟩).1 children)
    edge present with old | ⟨same, _⟩
  · exact heap key edge old
  · subst key
    simpa only [List.length_map] using checked

/-- Ordinary node normalization does not change the edge-record table. -/
theorem node_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (edges : List (EdgeValue Symbol Constraint)) (state : State Symbol Constraint)
    (heap : Heap state) : Heap (run (makeNode edges) state).2 := by
  simp only [makeNode]
  split <;> exact heap

/-- Union normalization retains every projected edge-arity fact. -/
theorem union_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (values : List (Value Symbol Constraint)) (state : State Symbol Constraint)
    (heap : Heap state) : Heap (run (makeUnion values) state).2 := by
  unfold makeUnion
  split <;> first | exact heap | (split <;> first | exact heap | exact node_heap _ state heap)

/-- Removing a bare self reference retains the edge-arity facts. -/
theorem filter_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (name : InternedBinderProtocol.Reference) (value : Value Symbol Constraint)
    (state : State Symbol Constraint) (heap : Heap state) :
    Heap (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact heap
  split
  · exact union_heap _ state heap
  · exact heap

/-- Sequential execution retains arity at its actual stopping cache. -/
theorem bind_heap (outcome : Outcome Symbol Constraint First)
    (next : First → State Symbol Constraint → Outcome Symbol Constraint Result)
    (heap : Heap outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- Canonical binder hits and actual callbacks retain edge-arity facts. -/
theorem request_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (smart : Bool) (depth ordinary : Value Symbol Constraint)
    (callback : InternedBinderProtocol.Reference → State Symbol Constraint →
      Outcome Symbol Constraint (Value Symbol Constraint))
    (state : State Symbol Constraint) (heap : Heap state)
    (checked : ∀ name current, Heap current → Heap (callback name current).state) :
    Heap (request smart depth ordinary callback state).state := by
  simp only [request]
  split
  · split <;> exact heap
  · apply bind_heap _ _
      (checked _ {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} heap)
    intro body after done afterHeap
    exact afterHeap

/-- Actual successful child construction retains the number of child plans. -/
theorem buildMany_length [DecidableEq (EdgeKey Symbol Constraint)]
    (expressions : List (Syntax Symbol Constraint)) (environment : List (Value Symbol Constraint))
    (state : State Symbol Constraint) (values : List (Value Symbol Constraint))
    (after : State Symbol Constraint)
    (done : buildMany expressions environment state = .done values after) :
    values.length = expressions.length := by
  induction expressions generalizing state values after with
  | nil =>
      simp only [buildMany] at done
      cases done
      rfl
  | cons first rest ih =>
      rw [buildMany] at done
      cases headRun : build first environment state with
      | pending key afterHead =>
          simp only [headRun, Outcome.bind] at done
          cases done
      | done value afterHead =>
          simp only [headRun, Outcome.bind] at done
          cases tailRun : buildMany rest environment afterHead with
          | pending key afterTail =>
              simp only [tailRun, Outcome.bind] at done
              cases done
          | done tail afterTail =>
              simp only [tailRun, Outcome.bind] at done
              have lengthSame := ih afterHead tail afterTail tailRun
              cases done
              simpa only [List.length_cons] using congrArg Nat.succ lengthSame

mutual
/-- Actual raw construction retains arity from checked source syntax. -/
theorem build_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (expression : Syntax Symbol Constraint) (environment : List (Value Symbol Constraint))
    (state : State Symbol Constraint) (heap : Heap state) (checked : Checked expression) :
    Heap (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using heap
  | node edges =>
      rw [build]
      apply bind_heap _ _ (buildEdges_heap edges environment state heap checked)
      intro values after done afterHeap
      exact node_heap values after afterHeap
  | union members =>
      rw [build]
      apply bind_heap _ _ (buildMany_heap members environment state heap checked)
      intro values after done afterHeap
      exact union_heap values after afterHeap
  | binder smart body =>
      have callback (name : InternedBinderProtocol.Reference) (current : State Symbol Constraint)
          (currentHeap : Heap current) :
          Heap ((build body (.reference name :: environment) current).bind
            fun value next => work (withoutSelfReference name value) next).state := by
        apply bind_heap _ _ (build_heap body _ current currentHeap checked)
        intro value after done afterHeap
        exact filter_heap name value after afterHeap
      rw [build]
      apply bind_heap _ _ (callback _ state heap)
      intro depth afterDepth doneDepth depthHeap
      apply bind_heap _ _ (callback _ afterDepth depthHeap)
      intro ordinary afterOrdinary doneOrdinary ordinaryHeap
      exact request_heap smart depth ordinary _ afterOrdinary ordinaryHeap callback
termination_by sizeOf expression

/-- Actual child-plan execution retains all checked edge keys. -/
theorem buildMany_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (expressions : List (Syntax Symbol Constraint)) (environment : List (Value Symbol Constraint))
    (state : State Symbol Constraint) (heap : Heap state) (checked : ManyChecked expressions) :
    Heap (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using heap
  | cons first rest =>
      rw [buildMany]
      apply bind_heap _ _ (build_heap first environment state heap checked.1)
      intro value after done afterHeap
      apply bind_heap _ _ (buildMany_heap rest environment after afterHeap checked.2)
      intro values final returned finalHeap
      exact finalHeap
termination_by sizeOf expressions

/-- Each actual new edge uses the checked syntactic count and the completed child-list length. -/
theorem buildEdges_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (expressions : List (EdgeSyntax Symbol Constraint)) (environment : List (Value Symbol Constraint))
    (state : State Symbol Constraint) (heap : Heap state) (checked : EdgesChecked expressions) :
    Heap (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_heap _ _ (buildMany_heap children environment state heap checked.2.1)
          intro values after done afterHeap
          have sameLength := buildMany_length children environment state values after done
          have currentChecked : Fits constraint values.length := by
            rw [sameLength]
            exact checked.1
          apply bind_heap (work (makeEdge symbol constraint values) after) _
            (edge_heap symbol constraint values after afterHeap currentChecked)
          intro edge afterEdge returned edgeHeap
          apply bind_heap _ _ (buildEdges_heap rest environment afterEdge edgeHeap checked.2.2)
          intro edges final returned finalHeap
          exact finalHeap
termination_by sizeOf expressions
end

/-- Checked closed initial syntax derives the complete actual edge-arity invariant. -/
theorem constructed_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (expression : Syntax Symbol Constraint) (checked : Checked expression)
    (value : Value Symbol Constraint) (state : State Symbol Constraint)
    (built : build expression [] empty = .done value state) : Heap state := by
  have preserved := build_heap expression [] empty empty_heap checked
  simpa only [built, Outcome.state] using preserved

/-- Stored child encoding retains the number of original children. -/
theorem encodeMany_length (context : List (Value Symbol Constraint))
    (locals : List InternedBinderProtocol.Reference) (values : List (Value Symbol Constraint)) :
    (encodeMany context locals values).length = values.length := by
  induction values with
  | nil => rfl
  | cons first rest ih => simpa only [encodeMany, List.length_cons] using congrArg Nat.succ ih

mutual
/-- Actual stored encoding checks each copied edge at its original child count. -/
theorem encode_checked (value : Value Symbol Constraint)
    (state : State Symbol Constraint) (facts : Facts state) (heap : Heap state)
    (available : Available state value) (context : List (Value Symbol Constraint))
    (locals : List InternedBinderProtocol.Reference) : Checked (encode context locals value) := by
  rw [encode.eq_def]
  split
  · trivial
  · cases value with
    | empty => trivial
    | reference name => split <;> first | trivial | (split <;> trivial)
    | node entry edges depth free =>
        exact encodeEdges_checked edges state facts heap
          (resident_edges state facts.linked (.node entry edges depth free) available.resident) context locals
    | union entry members depth free =>
        exact encodeMany_checked members state facts heap
          (fun child member => available.children child member) context locals
    | mu entry body depth ordinary =>
        exact encode_checked body state facts heap (available.children body (by simp [children])) context _
termination_by sizeOf value

/-- Stored child encoding retains every nested checked edge. -/
theorem encodeMany_checked (values : List (Value Symbol Constraint))
    (state : State Symbol Constraint) (facts : Facts state) (heap : Heap state)
    (available : ∀ value ∈ values, Available state value) (context : List (Value Symbol Constraint))
    (locals : List InternedBinderProtocol.Reference) : ManyChecked (encodeMany context locals values) := by
  cases values with
  | nil => simp only [encodeMany, ManyChecked]
  | cons first rest =>
      rw [encodeMany]
      exact ⟨encode_checked first state facts heap (available first List.mem_cons_self) context locals,
        encodeMany_checked rest state facts heap
          (fun child member => available child (List.mem_cons_of_mem _ member)) context locals⟩
termination_by sizeOf values

/-- Each encoded edge keeps its exact guard and the count stored in its coherent key. -/
theorem encodeEdges_checked (edges : List (EdgeValue Symbol Constraint))
    (state : State Symbol Constraint) (facts : Facts state) (heap : Heap state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (context : List (Value Symbol Constraint))
    (locals : List InternedBinderProtocol.Reference) : EdgesChecked (encodeEdges context locals edges) := by
  cases edges with
  | nil => simp only [encodeEdges, EdgesChecked]
  | cons first rest =>
      cases first with
      | mk entry values =>
          rw [encodeEdges]
          have stored := resident (.mk entry values) List.mem_cons_self
          have arity := heap.edge state facts.coherent (.mk entry values) stored
          refine ⟨?_, encodeMany_checked values state facts heap
            (facts.cached.edges entry.key (.mk entry values) stored) context locals,
            encodeEdges_checked rest state facts heap
              (fun edge member => resident edge (List.mem_cons_of_mem _ member)) context locals⟩
          simpa only [encodeMany_length] using arity
termination_by sizeOf edges
end

/-- Actual stored execution preserves arity through every completed or pending reconstruction prefix. -/
theorem execute_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (value : Value Symbol Constraint) (environment : Environment Symbol Constraint)
    (state : State Symbol Constraint) (facts : Facts state) (heap : Heap state)
    (available : Available state value) :
    Heap (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state :=
  build_heap _ _ state heap (encode_checked value state facts heap available _ [])

/-- Actual cold unfolding retains arity for copied guards and same-length child plans. -/
theorem unfold_heap [DecidableEq (EdgeKey Symbol Constraint)]
    (value : Value Symbol Constraint) (state : State Symbol Constraint) (facts : Facts state)
    (heap : Heap state) (available : Available state value) :
    Heap (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact heap
  | mu entry body depth ordinary =>
      exact execute_heap body _ state facts heap (available.children body (by simp [children]))

end MicroCFTA.SourcePruningEnumerationArityOrigins
