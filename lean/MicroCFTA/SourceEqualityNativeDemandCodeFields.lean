import MicroCFTA.SourceEqualityNativeDemandFieldHeap

/-!
# Normalized annotations in compiled checked continuations

Original node compilation adds no unchecked edge annotation. Ordered walks
and arbitrary appended continuations retain this property. The accepted
edge code requires the normalized annotation derived by its actual prefix.
-/
namespace MicroCFTA.SourceEqualityNativeDemandCodeFields
open InternedConstructorTemplates SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemandFieldHeap (WorkFields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Every possible raw work instruction in a continuation has normalized new annotations. -/
def Fields : Code Symbol Guard Output → Prop
  | .pure _ | .fail _ => True
  | .work job next => WorkFields job ∧ ∀ value, Fields (next value)
  | .enter _ _ _ _ _ next => ∀ value, Fields (next value)
  | .read _ next => ∀ value, Fields (next value)
  | .optionalBinder _ _ next => ∀ value, Fields (next value)
  | .node _ next => ∀ value, Fields (next value)
  | .edge _ next => ∀ value, Fields (next value)
  | .finishNode _ _ next | .finishEdge _ _ next => Fields next

/-- Sequencing retains normalized annotations through all emitted continuations. -/
theorem fields_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (fields : Fields code) (continuations : ∀ value, Fields (next value)) : Fields (code.bind next) := by
  induction code with
  | pure value => exact continuations value
  | fail => trivial
  | work job resume ih => exact ⟨fields.1, fun value => ih value (fields.2 value)⟩
  | enter domain left right first second resume ih | read name resume ih | optionalBinder key body resume ih | node request resume ih | edge request resume ih =>
      exact fun value => ih value (fields value)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih fields

/-- Ordered source calls retain normalized annotations in every child continuation. -/
theorem fields_walk (call : A → Code Symbol Guard B) (inputs : List A)
    (calls : ∀ input ∈ inputs, Fields (call input)) : Fields (SourceRecursiveIntersectionCode.walk call inputs) := by
  induction inputs with
  | nil => trivial
  | cons first rest ih =>
      apply fields_bind _ _ (calls first List.mem_cons_self)
      intro value
      apply fields_bind _ _ (ih (fun input member => calls input (List.mem_cons_of_mem _ member)))
      intro values
      trivial

/-- Source Mu compilation adds only domain entry, recursive demand, and optional-binder instructions. -/
theorem compileMu_fields (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : Value Symbol Guard) : Fields (compileMu domain left right) := by
  unfold compileMu
  split <;> simp only [Fields, unsupported, implies_true]

/-- Source reference compilation adds no new edge annotation. -/
theorem compileReference_fields (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (name : Nat) (other : Value Symbol Guard) (left : Bool) : Fields (compileReference domain name other left) := by
  unfold compileReference
  split
  · intro found
    cases found with
    | none => trivial
    | some bound => split <;> intro value <;> trivial
  · trivial

/-- Original row joining adds only edge requests and ordinary node normalization. -/
theorem compileRows_fields [DecidableEq Symbol] (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : List (EdgeValue Symbol Guard)) : Fields (compileRows domain left right) := by
  apply fields_bind
  · exact fields_walk _ _ (fun _ _ => by intro value; trivial)
  · intro values
    exact ⟨SourceEqualityNativeDemandFieldHeap.makeNode_fields values, fun _ => trivial⟩

/-- Every actual source node branch emits normalized raw work annotations. -/
theorem compileNode_fields [DecidableEq Symbol] (request : NodeRequest Symbol Guard) : Fields (compileNode request) := by
  cases selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right with
  | empty | reset | self | swap | repeated key | unsupported =>
      simp only [compileNode, selected, unsupported, requestNode, Fields, implies_true]
  | bothMu | leftMu | rightMu => simpa only [compileNode, selected] using compileMu_fields request.domain request.left request.right
  | leftUnion =>
      simp only [compileNode, selected]
      cases request.left with
      | union entry members depth free =>
          apply fields_bind
          · exact fields_walk _ _ (fun _ _ => by intro value; trivial)
          · intro values
            exact ⟨SourceEqualityNativeDemandFieldHeap.makeUnion_fields values, fun _ => trivial⟩
      | empty | reference | node | mu => trivial
  | rightUnion =>
      simp only [compileNode, selected]
      cases request.right with
      | union entry members depth free =>
          apply fields_bind
          · exact fields_walk _ _ (fun _ _ => by intro value; trivial)
          · intro values
            exact ⟨SourceEqualityNativeDemandFieldHeap.makeUnion_fields values, fun _ => trivial⟩
      | empty | reference | node | mu => trivial
  | leftReference =>
      simp only [compileNode, selected]
      cases request.left <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_fields _ _ _ _ | trivial
  | rightReference =>
      simp only [compileNode, selected]
      cases request.right <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_fields _ _ _ _ | trivial
  | ordinary =>
      simp only [compileNode, selected]
      cases request.left <;> cases request.right <;> first | exact compileRows_fields _ _ _ | trivial

/-- The source sentinel's actual annotation is normalized by its empty-field constructor. -/
theorem sentinel_fields (left : EdgeValue Symbol Guard) : Fields (SourceEqualityNativeCheckedCode.sentinel left) :=
  ⟨SourceEqualityNativeDemandFieldHeap.makeEdge_fields _ _ _ SourceEqualityConstraintConstructors.top_cached, fun _ => trivial⟩

/-- A normalized actual prefix result supplies all annotations in the accepted child code. -/
theorem children_fields (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : EdgeValue Symbol Guard) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (cached : SourceEqualityGuardReadback.Cached (SourceEqualityConjoinAllocation.readback combined).equalities) :
    Fields (SourceEqualityNativeCheckedCode.children domain left right combined) := by
  apply fields_bind
  · exact fields_walk _ _ (fun _ _ => by intro value; trivial)
  · intro values
    exact ⟨SourceEqualityNativeDemandFieldHeap.makeEdge_fields _ _ _ cached, fun _ => trivial⟩

end MicroCFTA.SourceEqualityNativeDemandCodeFields
