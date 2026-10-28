import MicroCFTA.SourceEqualityAnnotationLanguage

/-!
# Source annotation invariants in actual constructor caches

The invariant belongs to physical edge-record keys. Canonical hits retain
those keys. Actual linked available records derive every semantic annotation
from this cache invariant. Safe constructor work preserves it at each prefix.
-/
namespace MicroCFTA.SourceEqualityAnnotationHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency SourceEqualityAnnotationLanguage

/-- Every actual physical edge key in the constructor cache satisfies the annotation predicate. -/
def Heap (valid : Guard → Prop) (state : State Symbol Guard) : Prop :=
  ∀ key edge, state.edgeRecords key = some edge → valid key.constraint

/-- The empty constructor cache satisfies every source annotation invariant. -/
theorem empty_heap (valid : Guard → Prop) : Heap valid (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key edge impossible
  cases impossible

/-- Original actual linked records derive their complete semantic annotation invariant from the cache. -/
theorem available (valid : Guard → Prop) (state : State Symbol Guard) (heap : Heap valid state) (linked : Linked state)
    (value : Value Symbol Guard) (resident : Available state value) : Annotated valid value := by
  induction resident with
  | intro value resident issued children ih =>
      cases value with
      | empty => exact .empty
      | reference name => exact .reference name
      | node entry edges depth free =>
          apply Annotated.node
          · intro edge member
            exact heap edge.entry.key edge (resident_edges state linked _ resident edge member)
          · simpa only [InternedProbeProvenance.children] using ih
      | union entry members depth free => exact .union entry members depth free (by simpa only [InternedProbeProvenance.children] using ih)
      | mu entry body depth ordinary => exact .mu entry body depth ordinary (ih body (by simp [InternedProbeProvenance.children]))

/-- A checked actual edge derives its own guard and each child annotation from the same physical heap. -/
theorem edge (valid : Guard → Prop) (state : State Symbol Guard) (heap : Heap valid state) (facts : InternedNestedFacts.Facts state)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident state edge) :
    valid edge.entry.key.constraint ∧ ∀ child ∈ edge.children, Annotated valid child :=
  ⟨heap edge.entry.key edge resident, fun child member => available valid state heap facts.linked child (facts.cached.edges _ edge resident child member)⟩

/-- One actual edge interning request retains the annotation invariant, including canonical hits. -/
theorem edgeStep [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (key : EdgeKey Symbol Guard) (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard)
    (state : State Symbol Guard) (heap : Heap valid state) (annotation : valid key.constraint) :
    Heap valid (InternedConstructorTemplates.edgeStep key identify state).2 := by
  intro other edge present
  rcases record_cases state.edgeRecords key other _ edge present with old | ⟨same, _⟩
  · exact heap other edge old
  · simpa only [same] using annotation

/-- Actual node allocation leaves every physical edge record unchanged. -/
theorem nodeStep (valid : Guard → Prop) (key : InternedBinderProtocol.NodeKey)
    (identify : Interned InternedBinderProtocol.NodeKey → Value Symbol Guard) (state : State Symbol Guard) (heap : Heap valid state) :
    Heap valid (InternedConstructorTemplates.nodeStep key identify state).2 := heap

/-- Constructor work emits only guards that satisfy the source annotation predicate. -/
def SafeWork (valid : Guard → Prop) : Work Symbol Guard A → Prop
  | .pure _ => True
  | .edge key _ next => valid key.constraint ∧ ∀ value, SafeWork valid (next value)
  | .node _ _ next => ∀ value, SafeWork valid (next value)

/-- Every actual constructor prefix preserves valid edge annotations under its emitted guard checks. -/
theorem run [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (work : Work Symbol Guard A)
    (safe : SafeWork valid work) (state : State Symbol Guard) (heap : Heap valid state) :
    Heap valid (InternedConstructorTemplates.run work state).2 := by
  induction work generalizing state with
  | pure value => exact heap
  | edge key identify next ih => exact ih _ (safe.2 _) _ (edgeStep valid key identify state heap safe.1)
  | node key identify next ih => exact ih _ (safe _) _ (nodeStep valid key identify state heap)

/-- Sequencing safe constructor computations retains every emitted annotation check. -/
theorem bind (valid : Guard → Prop) (work : Work Symbol Guard A) (next : A → Work Symbol Guard B)
    (safe : SafeWork valid work) (later : ∀ value, SafeWork valid (next value)) : SafeWork valid (work.bind next) := by
  induction work with
  | pure value => exact later value
  | edge key identify resume ih => exact ⟨safe.1, fun value => ih value (safe.2 value)⟩
  | node key identify resume ih => exact fun value => ih value (safe value)

/-- Literal makeEdge emits exactly its original complete source guard. -/
theorem makeEdge (valid : Guard → Prop) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (annotation : valid guard) : SafeWork valid (InternedConstructorTemplates.makeEdge symbol guard values) := ⟨annotation, fun _ => trivial⟩

/-- Actual ordinary-node construction emits no new edge annotation. -/
theorem makeNode (valid : Guard → Prop) (edges : List (EdgeValue Symbol Guard)) :
    SafeWork valid (InternedConstructorTemplates.makeNode edges) := by
  unfold InternedConstructorTemplates.makeNode
  dsimp only
  split <;> simp only [SafeWork, implies_true]

/-- Actual union construction reuses existing edge records in every normalization branch. -/
theorem makeUnion (valid : Guard → Prop) (values : List (Value Symbol Guard)) :
    SafeWork valid (InternedConstructorTemplates.makeUnion values) := by
  unfold InternedConstructorTemplates.makeUnion
  split
  · trivial
  · trivial
  · split
    · exact makeNode valid _
    · exact fun _ => trivial

/-- Source bare-self removal constructs only nodes and unions of existing edges. -/
theorem withoutSelfReference (valid : Guard → Prop) (name : InternedBinderProtocol.Reference) (value : Value Symbol Guard) :
    SafeWork valid (InternedConstructorTemplates.withoutSelfReference name value) := by
  cases value with
  | empty | reference | node | mu => trivial
  | union entry members depth free =>
      unfold InternedConstructorTemplates.withoutSelfReference
      split
      · exact makeUnion valid _
      · trivial

end MicroCFTA.SourceEqualityAnnotationHeap
