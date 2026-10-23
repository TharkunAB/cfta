import MicroCFTA.SourceCurrentConjunctionEquality
import MicroCFTA.SourceEqualityNativeCheckedCode
import MicroCFTA.SourceRecursiveIntersectionMaybeMu
import MicroCFTA.InternedFreshOrdinaryStoredConstraintHeap

/-!
# Existing allocated fields in native continuations

Each emitted edge annotation has an existing load in the indexed equality
cache. Actual cache growth retains these loads. Node compilation emits no
new edge annotation. Accepted child code uses the actual combined field
receipt. The rejected branch uses an explicit receipt for the source top.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCodeFields
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
local notation "OpState" => SourceEqualityConstraintMemoAllocation.State
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Every emitted raw edge annotation has a successful load in the current operation cache. -/
def Fields (operations : OpState) : Code Symbol Guard Output → Prop
  | .pure _ | .fail _ => True
  | .work job next => SourceEqualityAnnotationHeap.SafeWork (SourceCurrentConjunctionEquality.FieldAvailable operations) job ∧
      ∀ value, Fields operations (next value)
  | .enter _ _ _ _ _ next => ∀ value, Fields operations (next value)
  | .read _ next => ∀ value, Fields operations (next value)
  | .optionalBinder _ _ next => ∀ value, Fields operations (next value)
  | .node _ next => ∀ value, Fields operations (next value)
  | .edge _ next => ∀ value, Fields operations (next value)
  | .finishNode _ _ next | .finishEdge _ _ next => Fields operations next

/-- Actual equality-cache growth retains every emitted raw work annotation and its existing load. -/
theorem work_fields_grows (operations after : OpState) (job : Work Symbol Guard X)
    (fields : SourceEqualityAnnotationHeap.SafeWork (SourceCurrentConjunctionEquality.FieldAvailable operations) job)
    (growth : SourceEqualityConstraintMemoAllocation.Grows operations after) :
    SourceEqualityAnnotationHeap.SafeWork (SourceCurrentConjunctionEquality.FieldAvailable after) job := by
  induction job with
  | pure => trivial
  | edge key identify next ih => exact ⟨fields.1.grows growth, fun value => ih value (fields.2 value)⟩
  | node key identify next ih => exact fun value => ih value (fields value)

/-- Every possible continuation retains its allocated-field receipts through actual cache growth. -/
theorem fields_grows (operations after : OpState) (code : Code Symbol Guard A)
    (fields : Fields operations code) (growth : SourceEqualityConstraintMemoAllocation.Grows operations after) :
    Fields after code := by
  induction code with
  | pure | fail => trivial
  | work job next ih =>
      exact ⟨work_fields_grows operations after job fields.1 growth, fun value => ih value (fields.2 value)⟩
  | enter domain left right first second next ih | read name next ih | optionalBinder key body next ih | node request next ih | edge request next ih => exact fun value => ih value (fields value)
  | finishNode handle value next ih | finishEdge handle value next ih => exact ih fields

/-- Sequencing retains same-cache field receipts through each emitted continuation. -/
theorem fields_bind (operations : OpState) (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (fields : Fields operations code) (continuations : ∀ value, Fields operations (next value)) :
    Fields operations (code.bind next) := by
  induction code with
  | pure value => exact continuations value
  | fail => trivial
  | work job resume ih => exact ⟨fields.1, fun value => ih value (fields.2 value)⟩
  | enter domain left right first second resume ih | read name resume ih | optionalBinder key body resume ih | node request resume ih | edge request resume ih => exact fun value => ih value (fields value)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih fields

/-- Ordered source calls retain allocated fields in each child continuation. -/
theorem fields_walk (operations : OpState) (call : A → Code Symbol Guard B) (inputs : List A)
    (calls : ∀ input ∈ inputs, Fields operations (call input)) :
    Fields operations (SourceRecursiveIntersectionCode.walk call inputs) := by
  induction inputs with
  | nil => trivial
  | cons first rest ih =>
      apply fields_bind operations _ _ (calls first List.mem_cons_self)
      intro value
      apply fields_bind operations _ _ (ih (fun input member => calls input (List.mem_cons_of_mem _ member)))
      intro values
      trivial

/-- Direct source edge construction uses its actual existing field load. -/
theorem makeEdge_fields (operations : OpState) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (available : SourceCurrentConjunctionEquality.FieldAvailable operations guard) :
    SourceEqualityAnnotationHeap.SafeWork (SourceCurrentConjunctionEquality.FieldAvailable operations) (makeEdge symbol guard values) :=
  SourceEqualityAnnotationHeap.makeEdge _ symbol guard values available

/-- Ordinary node construction emits no new edge annotation. -/
theorem makeNode_fields (operations : OpState) (edges : List (EdgeValue Symbol Guard)) :
    SourceEqualityAnnotationHeap.SafeWork (SourceCurrentConjunctionEquality.FieldAvailable operations) (makeNode edges) :=
  SourceEqualityAnnotationHeap.makeNode _ edges

/-- Union normalization emits no new edge annotation in any branch. -/
theorem makeUnion_fields (operations : OpState) (values : List (Value Symbol Guard)) :
    SourceEqualityAnnotationHeap.SafeWork (SourceCurrentConjunctionEquality.FieldAvailable operations) (makeUnion values) :=
  SourceEqualityAnnotationHeap.makeUnion _ values

/-- Source Mu compilation emits only domain entry, recursive demand, and optional binding. -/
theorem compileMu_fields (operations : OpState) (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : Value Symbol Guard) : Fields operations (compileMu domain left right) := by
  unfold compileMu
  split <;> simp only [Fields, unsupported, implies_true]

/-- Source reference compilation emits no new edge annotation. -/
theorem compileReference_fields (operations : OpState) (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (name : Nat) (other : Value Symbol Guard) (left : Bool) :
    Fields operations (compileReference domain name other left) := by
  unfold compileReference
  split
  · intro found
    cases found with
    | none => trivial
    | some bound => split <;> intro value <;> trivial
  · trivial

/-- Row joining emits only edge requests and ordinary node normalization. -/
theorem compileRows_fields [DecidableEq Symbol] (operations : OpState)
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey) (left right : List (EdgeValue Symbol Guard)) :
    Fields operations (compileRows domain left right) := by
  apply fields_bind operations
  · exact fields_walk operations _ _ (fun _ _ => by intro value; trivial)
  · intro values
    exact ⟨makeNode_fields operations values, fun _ => trivial⟩

/-- Every literal source node branch emits only fields already available in the indexed cache. -/
theorem compileNode_fields [DecidableEq Symbol] (operations : OpState) (request : NodeRequest Symbol Guard) :
    Fields operations (compileNode request) := by
  cases selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right with
  | empty | reset | self | swap | repeated key | unsupported =>
      simp only [compileNode, selected, unsupported, requestNode, Fields, implies_true]
  | bothMu | leftMu | rightMu =>
      simpa only [compileNode, selected] using compileMu_fields operations request.domain request.left request.right
  | leftUnion =>
      simp only [compileNode, selected]
      cases request.left with
      | union entry members depth free =>
          apply fields_bind operations
          · exact fields_walk operations _ _ (fun _ _ => by intro value; trivial)
          · intro values
            exact ⟨makeUnion_fields operations values, fun _ => trivial⟩
      | empty | reference | node | mu => trivial
  | rightUnion =>
      simp only [compileNode, selected]
      cases request.right with
      | union entry members depth free =>
          apply fields_bind operations
          · exact fields_walk operations _ _ (fun _ _ => by intro value; trivial)
          · intro values
            exact ⟨makeUnion_fields operations values, fun _ => trivial⟩
      | empty | reference | node | mu => trivial
  | leftReference =>
      simp only [compileNode, selected]
      cases request.left <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_fields operations _ _ _ _ | trivial
  | rightReference =>
      simp only [compileNode, selected]
      cases request.right <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_fields operations _ _ _ _ | trivial
  | ordinary =>
      simp only [compileNode, selected]
      cases request.left <;> cases request.right <;> first | exact compileRows_fields operations _ _ _ | trivial

/-- The actual rejected branch uses an existing load for its source top annotation. -/
theorem sentinel_fields (operations : OpState) (left : EdgeValue Symbol Guard)
    (available : SourceCurrentConjunctionEquality.FieldAvailable operations (SourceEqualityConstraintConstructors.top : Guard)) :
    Fields operations (SourceEqualityNativeCheckedCode.sentinel left) :=
  ⟨makeEdge_fields operations _ _ _ available, fun _ => trivial⟩

/-- The accepted child code retains the actual combined annotation's existing same-cache load. -/
theorem children_fields (operations : OpState) (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : EdgeValue Symbol Guard) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (available : SourceCurrentConjunctionEquality.FieldAvailable operations (SourceEqualityConjoinAllocation.readback combined)) :
    Fields operations (SourceEqualityNativeCheckedCode.children domain left right combined) := by
  apply fields_bind operations
  · exact fields_walk operations _ _ (fun _ _ => by intro value; trivial)
  · intro values
    exact ⟨makeEdge_fields operations _ _ _ available, fun _ => trivial⟩

/-- Every finite raw work prefix retains existing field loads at its actual constructor heap. -/
theorem work_heap [DecidableEq (EdgeKey Symbol Guard)] (operations : OpState) (job : Work Symbol Guard X)
    (state : InternedConstructorTemplates.State Symbol Guard) (heap : SourceCurrentConjunctionEquality.Fields operations state)
    (fields : SourceEqualityAnnotationHeap.SafeWork (SourceCurrentConjunctionEquality.FieldAvailable operations) job) :
    SourceCurrentConjunctionEquality.Fields operations (run job state).2 :=
  SourceEqualityAnnotationHeap.run _ job fields state heap

/-- Ordinary node normalization retains physical same-cache field availability. -/
theorem makeNode_heap [DecidableEq (EdgeKey Symbol Guard)] (operations : OpState)
    (edges : List (EdgeValue Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (heap : SourceCurrentConjunctionEquality.Fields operations state) : SourceCurrentConjunctionEquality.Fields operations (run (makeNode edges) state).2 :=
  work_heap operations _ state heap (makeNode_fields operations edges)

/-- Union normalization retains physical same-cache field availability. -/
theorem makeUnion_heap [DecidableEq (EdgeKey Symbol Guard)] (operations : OpState)
    (values : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (heap : SourceCurrentConjunctionEquality.Fields operations state) : SourceCurrentConjunctionEquality.Fields operations (run (makeUnion values) state).2 :=
  work_heap operations _ state heap (makeUnion_fields operations values)

/-- Actual optional binding copies only resident annotations with existing current-cache loads. -/
theorem optionalBinder_heap [DecidableEq (EdgeKey Symbol Guard)] (operations : OpState) (pair : Nat × Nat)
    (value : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (heap : SourceCurrentConjunctionEquality.Fields operations state) (available : Available state value) :
    SourceCurrentConjunctionEquality.Fields operations (SourceRecursiveIntersectionMaybeMu.maybeMu pair value state).state := by
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair value state state facts available]
  split
  · apply InternedFreshOrdinaryConstraintHeap.build_heap _ _ _ state heap
    exact InternedFreshOrdinaryStoredConstraintHeap.encode_valid _ value state facts heap available _ _
  · exact heap

end MicroCFTA.SourceCurrentAllocatedNativeCodeFields
