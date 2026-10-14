import MicroCFTA.InternedFreshOrdinaryConstraintHeap
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.InternedNestedFacts

/-!
# Constraint invariants through actual stored substitution

The stored encoder copies each resident edge constraint. Its reconstructed
lexical plan therefore satisfies the same invariant as the source cache.
Actual repaired substitution and unfolding retain that invariant.
-/
namespace MicroCFTA.InternedFreshOrdinaryStoredConstraintHeap
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedEdgeResidency
open InternedStoredSubstitution (Environment encode encodeMany encodeEdges)
open InternedFreshOrdinaryConstraintHeap

mutual
/-- The actual stored encoder copies only constraints from resident source edges. -/
theorem encode_valid (property : Guard → Prop) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (heap : Heap property state)
    (available : Available state value) (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference) :
    SyntaxValid property (encode context locals value) := by
  rw [encode.eq_def]
  split
  · trivial
  · cases value with
    | empty => trivial
    | reference name => split <;> first | trivial | (split <;> trivial)
    | node entry edges depth free =>
        exact encodeEdges_valid property edges state facts heap
          (resident_edges state facts.linked (.node entry edges depth free) available.resident) context locals
    | union entry members depth free =>
        exact encodeMany_valid property members state facts heap (fun child member => available.children child member) context locals
    | mu entry body depth ordinary =>
        exact encode_valid property body state facts heap (available.children body (by simp [children])) context _
termination_by sizeOf value

/-- Stored child plans retain every resident constraint in its original position. -/
theorem encodeMany_valid (property : Guard → Prop) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (heap : Heap property state)
    (available : ∀ value ∈ values, Available state value) (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference) :
    ManyValid property (encodeMany context locals values) := by
  cases values with
  | nil => simp only [encodeMany, ManyValid]
  | cons first rest =>
      rw [encodeMany]
      exact ⟨encode_valid property first state facts heap (available first List.mem_cons_self) context locals,
        encodeMany_valid property rest state facts heap (fun child member => available child (List.mem_cons_of_mem _ member)) context locals⟩
termination_by sizeOf values

/-- Each stored edge plan retains its exact canonical constraint. -/
theorem encodeEdges_valid (property : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (heap : Heap property state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference) :
    EdgesValid property (encodeEdges context locals edges) := by
  cases edges with
  | nil => simp only [encodeEdges, EdgesValid]
  | cons first rest =>
      cases first with
      | mk entry values =>
          rw [encodeEdges]
          have stored := resident (.mk entry values) List.mem_cons_self
          exact ⟨heap entry.key (.mk entry values) stored,
            encodeMany_valid property values state facts heap
              (facts.cached.edges entry.key (.mk entry values) stored) context locals,
            encodeEdges_valid property rest state facts heap (fun edge member => resident edge (List.mem_cons_of_mem _ member)) context locals⟩
termination_by sizeOf edges
end

/-- Actual repaired stored substitution retains the complete edge-constraint cache invariant. -/
theorem execute_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop) (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (heap : Heap property state) (available : Available state value) :
    Heap property (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state :=
  build_heap property _ _ state heap (encode_valid property value state facts heap available _ [])

/-- Actual repaired unfolding retains every original edge constraint, including nested Mu reconstruction. -/
theorem unfold_heap [DecidableEq (EdgeKey Symbol Guard)] (property : Guard → Prop) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (heap : Heap property state) (available : Available state value) :
    Heap property (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact heap
  | mu entry body depth ordinary =>
      exact execute_heap property body _ state facts heap (available.children body (by simp [children]))

end MicroCFTA.InternedFreshOrdinaryStoredConstraintHeap
