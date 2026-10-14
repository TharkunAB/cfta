import MicroCFTA.SourceRecursiveIntersectionResultScope

/-!
# Actual successful source effects retain semantic heaps and result scope

The observations concern actual completed outcomes. Ordered walks pass each
returned semantic heap to the remaining requests. Existing physical checks
supply availability, valid states, and exact growth at those source points.
-/
namespace MicroCFTA.SourceRecursiveIntersectionScopeEffects
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)

/-- An actual returned result retains the complete semantic heap and its specified result property. -/
def Observed (result : Result Symbol Guard A) (post : A → Prop) : Prop :=
  ∀ value after, result = .done value after → SemanticHeap after.heap ∧ post value

/-- A source failure has no returned result obligation. -/
theorem failed (failure : Failure) (state : Machine Symbol Guard) (post : A → Prop) :
    Observed (.failed failure state) post := by intro value after impossible; cases impossible

/-- A literal source return retains its original complete semantic heap. -/
theorem pure (state : Machine Symbol Guard) (heap : SemanticHeap state.heap) (value : A) (post : A → Prop) (property : post value) :
    Observed (.done value state) post := by
  intro actual after same
  cases same
  exact ⟨heap, property⟩

/-- Sequential actual returns pass the complete semantic heap and result property to their continuation. -/
theorem bind (result : Result Symbol Guard A) (next : A → Machine Symbol Guard → Result Symbol Guard B)
    (first : A → Prop) (post : B → Prop) (observed : Observed result first)
    (later : ∀ value after, result = .done value after → SemanticHeap after.heap → first value → Observed (next value after) post) :
    Observed (result.bind next) post := by
  cases result with
  | failed failure after => exact failed failure after post
  | done value after =>
      have returned := observed value after rfl
      exact later value after rfl returned.1 returned.2

/-- An observed actual return can retain a weaker result property without changing its exact cache. -/
theorem map (result : Result Symbol Guard A) (first post : A → Prop) (observed : Observed result first)
    (convert : ∀ value, first value → post value) : Observed result post := by
  intro value after done
  have returned := observed value after done
  exact ⟨returned.1, convert value returned.2⟩

/-- Every successful ordered walk retains semantic heaps and each returned value's proved scope property. -/
theorem walk_observed (call : A → Machine Symbol Guard → Result Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (physical : Machine Symbol Guard → B → Prop) (post : B → Prop)
    (stable : Stable input)
    (checked : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → Checked state (call request state) physical)
    (observed : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → SemanticHeap state.heap → Observed (call request state) post)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (inputs : ∀ request ∈ requests, input state request)
    (heap : SemanticHeap state.heap) : Observed (walk call requests state) (fun values => ∀ value ∈ values, post value) := by
  induction requests generalizing state with
  | nil => exact pure state heap [] _ (by intro value member; cases member)
  | cons first rest ih =>
      have firstChecked := checked first List.mem_cons_self state valid (inputs first List.mem_cons_self)
      have firstObserved := observed first List.mem_cons_self state valid (inputs first List.mem_cons_self) heap
      rw [walk]
      apply bind _ _ post _ firstObserved
      intro value after done afterHeap present
      have afterValid : SourceRecursiveIntersectionKernel.Valid after := by simpa only [done, Result.state] using firstChecked.valid
      have growth : Extension state after := by simpa only [done, Result.state] using firstChecked.extension
      have restObserved := ih (fun request member => checked request (List.mem_cons_of_mem first member))
        (fun request member => observed request (List.mem_cons_of_mem first member)) after afterValid
        (fun request member => stable state after growth request (inputs request (List.mem_cons_of_mem first member))) afterHeap
      apply bind _ _ _ _ restObserved
      intro values final completed finalHeap restPresent
      apply pure final finalHeap
      intro actual member
      rcases List.mem_cons.mp member with rfl | included
      · exact present
      · exact restPresent actual included

/-- Actual edge work retains the semantic heap and the scopes of its available original children. -/
theorem edge_observed [DecidableEq (EdgeKey Symbol Guard)] (pairs : List (Nat × Nat)) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : Machine Symbol Guard) (heap : SemanticHeap state.heap)
    (available : ∀ value ∈ values, Available state.heap value) (scopes : ∀ value ∈ values, Scope pairs value) :
    Observed (work (makeEdge symbol guard values) state) (EdgeScope pairs) := by
  intro value after done
  cases done
  exact ⟨SourceRecursiveIntersectionSemanticHeap.edge symbol guard values state.heap heap available,
    SourceRecursiveIntersectionResultScope.edge pairs symbol guard values state.heap heap.1.normal.facts available scopes⟩

/-- Actual node work retains the semantic heap and only the scopes of surviving resident row children. -/
theorem node_observed [DecidableEq (EdgeKey Symbol Guard)] (pairs : List (Nat × Nat)) (edges : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (heap : SemanticHeap state.heap)
    (resident : ∀ edge ∈ edges, InternedEdgeResidency.EdgeResident state.heap edge) (scopes : ∀ edge ∈ edges, EdgeScope pairs edge) :
    Observed (work (makeNode edges) state) (Scope pairs) := by
  intro value after done
  cases done
  exact ⟨SourceRecursiveIntersectionSemanticHeap.node edges state.heap heap resident,
    SourceRecursiveIntersectionResultScope.node pairs edges state.heap heap.1.normal.facts resident scopes⟩

/-- Actual union work retains the semantic heap and only the scopes of available original operands. -/
theorem union_observed [DecidableEq (EdgeKey Symbol Guard)] (pairs : List (Nat × Nat)) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (heap : SemanticHeap state.heap)
    (available : ∀ value ∈ values, Available state.heap value) (scopes : ∀ value ∈ values, Scope pairs value) :
    Observed (work (makeUnion values) state) (Scope pairs) := by
  intro value after done
  cases done
  exact ⟨SourceRecursiveIntersectionSemanticHeap.union values state.heap heap available,
    SourceRecursiveIntersectionResultScope.union pairs values state.heap heap.1.normal available scopes⟩

/-- Actual optional-binder work retains the semantic heap and removes its newly inserted pair from scope. -/
theorem optional_observed [DecidableEq (EdgeKey Symbol Guard)] (pairs : List (Nat × Nat)) (pair : Nat × Nat)
    (body : Value Symbol Guard) (state : Machine Symbol Guard) (heap : SemanticHeap state.heap)
    (available : Available state.heap body) (scope : Scope (pair :: pairs) body) :
    Observed (construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.heap) state) (Scope pairs) := by
  have retained := SourceRecursiveIntersectionSemanticHeap.optionalBinder pair body state.heap heap available
  cases done : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.heap with
  | pending key after => exact failed (.pending key) _ _
  | done value after =>
      have afterHeap : SemanticHeap after := by simpa only [done, InternedNestedConstruction.Outcome.state] using retained
      exact pure _ afterHeap value _
        (SourceRecursiveIntersectionResultScope.optionalBinder pairs pair body state.heap heap.1 available scope value after done)

end MicroCFTA.SourceRecursiveIntersectionScopeEffects
