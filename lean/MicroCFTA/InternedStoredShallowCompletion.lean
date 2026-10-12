import MicroCFTA.InternedStoredUnfoldingRank

/-!
# Completion of actual shallow stored-body substitution

A body with cached Mu depth zero prepares no binder request. The complete
source executor therefore returns a canonical result without a pending
readback. This supplies both completion and strict unfolding rank for the
shallow fragment, rather than assuming successful reconstruction.
-/
namespace MicroCFTA.InternedStoredShallowCompletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedStoredSubstitution InternedStoredBodyInvariant InternedStoredUnfoldingRank
open InternedUnionNormalForm InternedStoredSelfFilter InternedUnionHeadGuard InternedGateRank
open InternedBinderProtocol (NodeKey)

mutual
/-- Original source expression contains no dynamic binder allocation. -/
def BinderFree : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesBinderFree edges
  | .union members => ManyBinderFree members
  | .binder .. => False
termination_by expression => sizeOf expression

/-- All ordered source children avoid binder allocation. -/
def ManyBinderFree : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => BinderFree first ∧ ManyBinderFree rest
termination_by expressions => sizeOf expressions

/-- Source edge allocation depends only on its binder-free child expressions. -/
def EdgesBinderFree : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyBinderFree children ∧ EdgesBinderFree rest
termination_by expressions => sizeOf expressions
end

mutual
/-- No binder-free source execution can reach a pending Mu cache lookup. -/
theorem build_complete [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (free : BinderFree expression) :
    ∃ value final, build expression environment state = .done value final := by
  cases expression with
  | empty | var => exact ⟨_, _, by rw [build]⟩
  | binder => simp [BinderFree] at free
  | node edges =>
      simp only [BinderFree] at free
      obtain ⟨values, after, completed⟩ := buildEdges_complete edges environment state free
      exact ⟨(run (makeNode values) after).1, (run (makeNode values) after).2, by simp only [build, completed, Outcome.bind, work]⟩
  | union members =>
      simp only [BinderFree] at free
      obtain ⟨values, after, completed⟩ := buildMany_complete members environment state free
      exact ⟨(run (makeUnion values) after).1, (run (makeUnion values) after).2, by simp only [build, completed, Outcome.bind, work]⟩
termination_by sizeOf expression

/-- Every binder-free ordered child plan completes before its next sibling. -/
theorem buildMany_complete [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (free : ManyBinderFree expressions) :
    ∃ values final, buildMany expressions environment state = .done values final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp [buildMany]⟩
  | cons first rest =>
      simp only [ManyBinderFree] at free
      obtain ⟨value, after, head⟩ := build_complete first environment state free.1
      obtain ⟨values, final, tail⟩ := buildMany_complete rest environment after free.2
      exact ⟨value :: values, final, by simp only [buildMany, head, Outcome.bind, tail]⟩
termination_by sizeOf expressions

/-- Both actual source caches complete every binder-free edge schedule. -/
theorem buildEdges_complete [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (free : EdgesBinderFree expressions) :
    ∃ edges final, buildEdges expressions environment state = .done edges final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp [buildEdges]⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesBinderFree] at free
          obtain ⟨values, after, head⟩ := buildMany_complete children environment state free.1
          let edge := run (makeEdge symbol constraint values) after
          obtain ⟨edges, final, tail⟩ := buildEdges_complete rest environment edge.2 free.2
          dsimp only [edge] at tail
          exact ⟨edge.1 :: edges, final, by simp only [buildEdges, head, Outcome.bind, work, tail, edge]⟩
termination_by sizeOf expressions
end

mutual
/-- Actual cached depth zero excludes every open Mu branch of the stored preparation. -/
theorem encode_zero (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (zero : value.depth = 0) : BinderFree (encode context locals value) := by
  rw [encode.eq_def]
  split
  · simp [BinderFree]
  · cases value with
    | empty => simp [BinderFree]
    | reference name => cases found : locals.findIdx? (· == name) <;> simp [found, BinderFree]
    | mu => simp [Value.depth] at zero
    | node entry edges depth free =>
        simp only [BinderFree]
        apply encodeEdges_zero context locals edges state coherent (fun value member => available.children value member)
        intro value member
        exact Nat.eq_zero_of_le_zero (zero ▸ InternedUnionSeparation.child_depth state coherent _ value available member)
    | union entry members depth free =>
        simp only [BinderFree]
        apply encodeMany_zero context locals members state coherent (fun value member => available.children value member)
        intro value member
        exact Nat.eq_zero_of_le_zero (zero ▸ InternedUnionSeparation.child_depth state coherent _ value available member)
termination_by sizeOf value

/-- Every actual child of a depth-zero stored record prepares no new binder. -/
theorem encodeMany_zero (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state values) (zero : ∀ value ∈ values, value.depth = 0) :
    ManyBinderFree (encodeMany context locals values) := by
  cases values with
  | nil => simp [encodeMany, ManyBinderFree]
  | cons first rest =>
      simp only [encodeMany, ManyBinderFree]
      exact ⟨encode_zero context locals first state coherent (available first (by simp)) (zero first (by simp)),
        encodeMany_zero context locals rest state coherent (fun value member => available value (by simp [member]))
          (fun value member => zero value (by simp [member]))⟩
termination_by sizeOf values

/-- Source cached child bounds exclude binders inside prepared edge declarations. -/
theorem encodeEdges_zero (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (zero : ∀ value ∈ edges.flatMap EdgeValue.children, value.depth = 0) :
    EdgesBinderFree (encodeEdges context locals edges) := by
  cases edges with
  | nil => simp [encodeEdges, EdgesBinderFree]
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [encodeEdges, EdgesBinderFree]
          exact ⟨encodeMany_zero context locals children state coherent
            (fun value member => available value (by simp [EdgeValue.children, member]))
            (fun value member => zero value (by simp [EdgeValue.children, member])),
            encodeEdges_zero context locals rest state coherent
            (fun value member => available value (by simp [EdgeValue.children, member]))
            (fun value member => zero value (by simp [EdgeValue.children, member]))⟩
termination_by sizeOf edges
end

/-- Full actual substitution of a shallow stored body completes for every replacement environment. -/
theorem execute_complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (zero : value.depth = 0) :
    ∃ result final, execute value environment state = .done result final :=
  build_complete _ _ state (encode_zero (leaves value) [] value state coherent available zero)

/-- A shallow stored open Mu supplies both actual unfolding completion and
strict rank decrease. No success, fuel, or output-rank hypothesis remains. -/
theorem unfold_complete_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (flat : Flat state) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary)) (zero : body.depth = 0)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value final ∧
      headRank value < headRank (.mu entry body depth ordinary) := by
  have bodyAvailable : Available state body := available.children body (by simp [InternedProbeProvenance.children])
  obtain ⟨value, final, completed⟩ := execute_complete body _ state facts.coherent bodyAvailable zero
  refine ⟨value, final, completed, ?_⟩
  have guarded := InternedStoredBodyInvariant.stored_guarded entry body depth ordinary state facts.coherent flat clean available zero opened
  have rank := execute_guarded_rank (.interned entry.identity) body (.mu entry body depth ordinary) state facts
    bodyAvailable available guarded value final completed
  simp [rank, headRank]

end MicroCFTA.InternedStoredShallowCompletion
