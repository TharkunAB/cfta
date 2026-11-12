import MicroCFTA.SourceEqualityProjectionRead
import MicroCFTA.SourceRecursiveIntersectionSourceProfile
import MicroCFTA.InternedStoredSubstitutionScope

namespace MicroCFTA.SourceNativeReadArityHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedEdgeResidency
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedFreshOrdinaryConstruction
open InternedNestedProvenance (Values Edges)
open InternedStoredSubstitution (Environment encode encodeMany encodeEdges)
open MergedFreshOrdinaryExposure
open SourceEqualityRequiredSemanticCache (SemanticReady)
variable {Symbol Guard : Type} {bound : Nat}

/-- Every actual stored edge has at most the current numerical child bound. -/
def Heap (bound : Nat) (state : State Symbol Guard) : Prop :=
  ∀ key edge, state.edgeRecords key = some edge → edge.children.length ≤ bound

mutual

private def Checked (bound : Nat) : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesChecked bound edges
  | .union members => ManyChecked bound members
  | .binder _ body => Checked bound body

private def ManyChecked (bound : Nat) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Checked bound first ∧ ManyChecked bound rest

private def EdgesChecked (bound : Nat) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest =>
      children.length ≤ bound ∧ ManyChecked bound children ∧ EdgesChecked bound rest
end

theorem edge_heap [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (constraint : Guard) (children : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap bound state)
    (checked : children.length ≤ bound) :
    Heap bound (run (makeEdge symbol constraint children) state).2 := by
  intro key edge present
  rcases record_cases state.edgeRecords ⟨symbol, children.map Value.referenceOf, constraint⟩ key
    (.mk (Cache.intern state.edges ⟨symbol, children.map Value.referenceOf, constraint⟩).1 children)
    edge present with old | same
  · exact heap key edge old
  · cases same.2
    exact checked

theorem node_heap [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (heap : Heap bound state) : Heap bound (run (makeNode edges) state).2 := by
  simp only [makeNode]
  split <;> exact heap

private theorem union_heap [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (heap : Heap bound state) : Heap bound (run (makeUnion values) state).2 := by
  unfold makeUnion
  split <;> first | exact heap | (split <;> first | exact heap | exact node_heap _ state heap)

private theorem filter_heap [DecidableEq (EdgeKey Symbol Guard)]
    (name : InternedBinderProtocol.Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap bound state) :
    Heap bound (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact heap
  split
  · exact union_heap _ state heap
  · exact heap

private theorem bind_heap (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (heap : Heap bound outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap bound after → Heap bound (next value after).state) :
    Heap bound (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

private theorem request_heap [DecidableEq (EdgeKey Symbol Guard)]
    (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : InternedBinderProtocol.Reference → State Symbol Guard →
      Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap bound state)
    (checked : ∀ name current, Heap bound current → Heap bound (callback name current).state) :
    Heap bound (request smart depth ordinary callback state).state := by
  simp only [request]
  split
  · split <;> exact heap
  · apply bind_heap _ _
      (checked _ {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} heap)
    intro body after done afterHeap
    exact afterHeap

private theorem buildMany_length [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (values : List (Value Symbol Guard))
    (after : State Symbol Guard)
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
              simp only [tailRun] at done
              cases done
          | done tail afterTail =>
              simp only [tailRun] at done
              have lengthSame := ih afterHead tail afterTail tailRun
              cases done
              simpa only [List.length_cons] using congrArg Nat.succ lengthSame

mutual

private theorem build_heap [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap bound state) (checked : Checked bound expression) :
    Heap bound (build expression environment state).state := by
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
      have callback (name : InternedBinderProtocol.Reference) (current : State Symbol Guard)
          (currentHeap : Heap bound current) :
          Heap bound ((build body (.reference name :: environment) current).bind
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

private theorem buildMany_heap [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap bound state) (checked : ManyChecked bound expressions) :
    Heap bound (buildMany expressions environment state).state := by
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

private theorem buildEdges_heap [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap bound state) (checked : EdgesChecked bound expressions) :
    Heap bound (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_heap _ _ (buildMany_heap children environment state heap checked.2.1)
          intro values after done afterHeap
          have sameLength := buildMany_length children environment state values after done
          have currentChecked : values.length ≤ bound := by
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

mutual

private theorem encode_checked (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (heap : Heap bound state)
    (available : Available state value) (context : List (Value Symbol Guard))
    (locals : List InternedBinderProtocol.Reference) : Checked bound (encode context locals value) := by
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

private theorem encodeMany_checked (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (heap : Heap bound state)
    (available : ∀ value ∈ values, Available state value) (context : List (Value Symbol Guard))
    (locals : List InternedBinderProtocol.Reference) : ManyChecked bound (encodeMany context locals values) := by
  cases values with
  | nil => simp only [encodeMany, ManyChecked]
  | cons first rest =>
      rw [encodeMany]
      exact ⟨encode_checked first state facts heap (available first List.mem_cons_self) context locals,
        encodeMany_checked rest state facts heap
          (fun child member => available child (List.mem_cons_of_mem _ member)) context locals⟩
termination_by sizeOf values

private theorem encodeEdges_checked (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (heap : Heap bound state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (context : List (Value Symbol Guard))
    (locals : List InternedBinderProtocol.Reference) : EdgesChecked bound (encodeEdges context locals edges) := by
  cases edges with
  | nil => simp only [encodeEdges, EdgesChecked]
  | cons first rest =>
      cases first with
      | mk entry values =>
          rw [encodeEdges]
          have stored := resident (.mk entry values) List.mem_cons_self
          have arity := heap entry.key (.mk entry values) stored
          refine ⟨?_, encodeMany_checked values state facts heap
            (facts.cached.edges entry.key (.mk entry values) stored) context locals,
            encodeEdges_checked rest state facts heap
              (fun edge member => resident edge (List.mem_cons_of_mem _ member)) context locals⟩
          simpa only [InternedStoredSubstitutionScope.encodeMany_length, EdgeValue.children] using arity
termination_by sizeOf edges
end

private theorem execute_heap [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (heap : Heap bound state)
    (available : Available state value) :
    Heap bound (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state :=
  build_heap _ _ state heap (encode_checked value state facts heap available _ [])

private theorem unfold_heap [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (heap : Heap bound state) (available : Available state value) :
    Heap bound (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact heap
  | mu entry body depth ordinary =>
      exact execute_heap body _ state facts heap (available.children body (by simp [children]))

open MergedSourceExposure (Result)

private theorem unfold_verified [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value) :
    Verified state (InternedFreshOrdinaryStoredSubstitution.unfold value state) Available := by
  cases value with
  | empty | reference | node | union => exact pure_verified state facts _ Available available
  | mu entry body depth ordinary =>
      apply InternedFreshOrdinaryFacts.build_verified _ _ state facts
      apply InternedStoredSubstitution.inputs_available body _ state
        (available.children body (by simp [children]))
      intro name replacement found
      simp only [] at found
      split at found
      · cases found; exact available
      · contradiction

private theorem collect_heap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (state : State Symbol Guard) (facts : Facts state) (heap : Heap bound state)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values state pending) :
    Heap bound (collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact heap
  | succ fuel ih =>
      cases pending with
      | nil => exact heap
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state facts heap seen rest restInputs
          | reference => exact heap
          | node entry edges depth free =>
              simpa only [collect, MergedFreshOrdinaryGuardedEffects.prepend_state] using ih state facts heap seen rest restInputs
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts heap seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, ite_eq_right visited] using
                  ih state facts heap (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts heap seen rest restInputs
              · have verified := unfold_verified (.mu entry body depth ordinary) state facts available
                have retained := unfold_heap
                  (.mu entry body depth ordinary) state facts heap available
                cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
                | pending key after =>
                    simpa only [collect, ite_eq_right visited, unfolded, Outcome.state, Result.state] using retained
                | done result after =>
                    have afterFacts : Facts after := by simpa only [unfolded, Outcome.state] using verified.facts
                    have afterHeap : Heap bound after := by simpa only [unfolded, Outcome.state] using retained
                    have nextInputs : Values after (result :: rest) := by
                      intro child member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact verified.result child after unfolded
                      · simpa only [unfolded, Outcome.state] using verified.available child (restInputs child member)
                    simpa only [collect, ite_eq_right visited, unfolded] using
                      ih after afterFacts afterHeap (entry.identity :: seen) (result :: rest) nextInputs

private theorem nodeEdges_heap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (heap : Heap bound state) (available : Available state value) :
    Heap bound (MergedFreshOrdinaryExposure.nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentFacts : Facts current)
      (currentHeap : Heap bound current) (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Heap bound (collect fuel current [] [root]).canonical.state := by
    rw [MergedFreshOrdinaryGuardedEffects.canonical_state]
    exact collect_heap fuel current currentFacts currentHeap [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact heap
  | union => exact fallback state facts heap _ available
  | mu entry body depth ordinary =>
      have verified := unfold_verified (.mu entry body depth ordinary) state facts available
      have retained := unfold_heap
        (.mu entry body depth ordinary) state facts heap available
      cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
      | pending key after =>
          simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded, Outcome.state, Result.state] using retained
      | done result after =>
          have afterFacts : Facts after := by simpa only [unfolded, Outcome.state] using verified.facts
          have afterHeap : Heap bound after := by simpa only [unfolded, Outcome.state] using retained
          have rootAvailable : Available after (.mu entry body depth ordinary) := by
            simpa only [unfolded, Outcome.state] using verified.available _ available
          have closure := fallback after afterFacts afterHeap (.mu entry body depth ordinary) rootAvailable
          cases result with
          | node => simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded, Result.state] using afterHeap
          | empty | reference | union | mu => simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded] using closure

/-- The current issued inventory derives its own numerical edge-child cap. -/
theorem initial_heap (state : State Symbol Guard) (facts : Facts state) :
    Heap (SourceRecursiveIntersectionSourceProfile.limits state).arity state := by
  intro key edge present
  have keyEq := (facts.coherent.edges key edge present).2.1
  have resident : EdgeResident state edge := by
    simpa only [EdgeResident, keyEq] using present
  exact SourceRecursiveIntersectionSourceProfile.edge_read_bound state facts edge.entry.identity edge
    (SourceRecursiveIntersectionSourceProfile.resident_read state facts edge resident)

/-- The same actual closed read retains the current cap and bounds every returned row. -/
theorem read_arity_heap [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard}
    {edges : List (EdgeValue Symbol Guard)}
    (trace : SourceEqualityProjectionRead.Read value before edges after)
    (semantic : SemanticReady before) (available : Available before value)
    (closed : value.free = []) (heap : Heap bound before) :
    Heap bound after ∧ ∀ edge ∈ edges, edge.children.length ≤ bound := by
  have checked := trace.verified semantic available closed
  have retained : Heap bound after := by
    cases trace with
    | done fuel actual =>
        have kept := nodeEdges_heap fuel value before semantic.ready.semantic.1.normal.facts heap available
        simpa only [actual, MergedSourceExposure.Result.state] using kept
  refine ⟨retained, ?_⟩
  intro edge member
  exact retained edge.entry.key edge (checked.2.2.1 edge member)

end MicroCFTA.SourceNativeReadArityHeap
