import MicroCFTA.SourceRecursiveIntersectionNativeEvaluationTrace

/-!
# Source bodies contain no native completion instructions

The compiler emits source effects and recursive requests. Only the native
driver adds completion frames. This distinction permits induction over
nested evaluations without treating arbitrary user code as a source body.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks

/-- Source body code contains no explicit native node or edge completion frame. -/
def BodyCode (code : Code Symbol Guard A) : Prop :=
  match code with
  | .pure _ | .fail _ => True
  | .work _ next | .enter _ _ _ _ _ next | .read _ next | .optionalBinder _ _ next | .node _ next | .edge _ next =>
      ∀ value, BodyCode (next value)
  | .finishNode .. | .finishEdge .. => False

/-- Appending source continuations does not introduce a native completion frame. -/
theorem bodyCode_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (body : BodyCode code) (continuation : ∀ value, BodyCode (next value)) : BodyCode (code.bind next) := by
  induction code with
  | pure value => exact continuation value
  | fail failure => trivial
  | work job resume ih | enter domain left right first second resume ih | read name resume ih | optionalBinder key stored resume ih | node request resume ih | edge request resume ih =>
    intro value
    exact ih value (body value)
  | finishNode | finishEdge => cases body

/-- Ordered source walks contain only source body instructions. -/
theorem bodyCode_walk (call : A → Code Symbol Guard B) (values : List A)
    (bodies : ∀ value ∈ values, BodyCode (call value)) : BodyCode (walk call values) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
    apply bodyCode_bind _ _ (bodies first List.mem_cons_self)
    intro value
    apply bodyCode_bind _ _ (ih (fun member present => bodies member (List.mem_cons_of_mem _ present)))
    intro values
    trivial

/-- Actual Mu compilation emits only domain, body-request, and optional-binder instructions. -/
theorem compileMu_bodyCode (domain : Interned DomainKey) (left right : Value Symbol Guard) : BodyCode (compileMu domain left right) := by
  cases first : SourceRecursiveIntersectionControl.identity left <;> cases second : SourceRecursiveIntersectionControl.identity right <;>
    simp only [compileMu, first, second, unsupported, BodyCode, implies_true]

/-- Original physical reference compilation contains no completion frame. -/
theorem compileReference_bodyCode (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool) :
    BodyCode (compileReference domain name other left) := by
  by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · simp only [compileReference, member, ite_true, BodyCode]
    intro found
    cases found with
    | none => trivial
    | some bound => cases left <;> simp only [Bool.false_eq_true, ite_false, ite_true, requestNode, BodyCode, implies_true]
  · simp only [compileReference, member, ite_false, BodyCode]

/-- Every guarded source edge body contains no native completion instruction. -/
theorem compileEdge_bodyCode (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (request : EdgeRequest Symbol Guard) :
    BodyCode (compileEdge emptyGuard conjoin request) := by
  unfold compileEdge
  split
  · apply bodyCode_bind
    · exact bodyCode_walk _ _ (fun _ _ => by intro value; trivial)
    · intro values value
      trivial
  · intro value
    trivial

/-- Actual row joining emits only recursive edge requests and source node construction. -/
theorem compileRows_bodyCode [DecidableEq Symbol] (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard)) :
    BodyCode (compileRows domain left right) := by
  apply bodyCode_bind
  · exact bodyCode_walk _ _ (fun _ _ => by intro value; trivial)
  · intro values value
    trivial

/-- Every branch of the complete physical source compiler is source body code. -/
theorem compileNode_bodyCode [DecidableEq Symbol] (request : NodeRequest Symbol Guard) : BodyCode (compileNode request) := by
  cases selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right with
  | empty | reset | self | swap | repeated key | unsupported =>
    simp only [compileNode, selected, unsupported, requestNode, BodyCode, implies_true]
  | bothMu | leftMu | rightMu => simpa only [compileNode, selected] using compileMu_bodyCode request.domain request.left request.right
  | leftUnion =>
    simp only [compileNode, selected]
    cases request.left with
    | union entry members depth free =>
      apply bodyCode_bind
      · exact bodyCode_walk _ _ (fun _ _ => by intro value; trivial)
      · intro values value
        trivial
    | empty | reference | node | mu => trivial
  | rightUnion =>
    simp only [compileNode, selected]
    cases request.right with
    | union entry members depth free =>
      apply bodyCode_bind
      · exact bodyCode_walk _ _ (fun _ _ => by intro value; trivial)
      · intro values value
        trivial
    | empty | reference | node | mu => trivial
  | leftReference =>
    simp only [compileNode, selected]
    cases request.left <;> try trivial
    rename_i name
    cases name <;> first | exact compileReference_bodyCode _ _ _ _ | trivial
  | rightReference =>
    simp only [compileNode, selected]
    cases request.right <;> try trivial
    rename_i name
    cases name <;> first | exact compileReference_bodyCode _ _ _ _ | trivial
  | ordinary =>
    simp only [compileNode, selected]
    cases request.left <;> cases request.right <;> first | exact compileRows_bodyCode _ _ _ | trivial

end MicroCFTA.SourceRecursiveIntersectionCode
