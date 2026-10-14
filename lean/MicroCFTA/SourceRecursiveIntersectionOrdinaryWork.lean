import MicroCFTA.SourceRecursiveIntersectionBodyCode
import MicroCFTA.SourceRecursiveIntersectionOpenDepthEffects

/-!
# Ordinary jobs in the actual recursive source compiler

The compiler puts all Mu allocation in explicit optional-binder instructions.
Every ordinary work instruction retains the previous complete Mu records.
This property follows all continuations and does not assume a heap invariant.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open InternedShallowHeap (NoNewMu)

/-- Source work instructions add no Mu, while explicit optional binders retain their own proved rule. -/
def OrdinaryWork [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) : Prop :=
  match code with
  | .pure _ | .fail _ => True
  | .work job next => (∀ state, NoNewMu state (run job state).2) ∧ ∀ value, OrdinaryWork (next value)
  | .enter _ _ _ _ _ next | .read _ next | .optionalBinder _ _ next | .node _ next | .edge _ next =>
      ∀ value, OrdinaryWork (next value)
  | .finishNode .. | .finishEdge .. => False

/-- Source sequencing retains the actual no-new-Mu job property in every continuation. -/
theorem ordinaryWork_bind [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (ordinary : OrdinaryWork code) (continuation : ∀ value, OrdinaryWork (next value)) : OrdinaryWork (code.bind next) := by
  induction code with
  | pure value => exact continuation value
  | fail failure => trivial
  | work job resume ih => exact ⟨ordinary.1, fun value => ih value (ordinary.2 value)⟩
  | enter domain left right first second resume ih | read name resume ih | optionalBinder key stored resume ih | node request resume ih | edge request resume ih =>
      intro value
      exact ih value (ordinary value)
  | finishNode | finishEdge => cases ordinary

/-- Ordered recursive walks retain ordinary jobs through every returned child. -/
theorem ordinaryWork_walk [DecidableEq (EdgeKey Symbol Guard)] (call : A → Code Symbol Guard B) (values : List A)
    (ordinary : ∀ value ∈ values, OrdinaryWork (call value)) : OrdinaryWork (walk call values) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      apply ordinaryWork_bind _ _ (ordinary first List.mem_cons_self)
      intro value
      apply ordinaryWork_bind _ _ (ih (fun member present => ordinary member (List.mem_cons_of_mem _ present)))
      intro values
      trivial

/-- Actual Mu compilation puts Mu allocation only in its explicit optional-binder instruction. -/
theorem compileMu_ordinaryWork [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (left right : Value Symbol Guard) :
    OrdinaryWork (compileMu domain left right) := by
  cases first : SourceRecursiveIntersectionControl.identity left <;> cases second : SourceRecursiveIntersectionControl.identity right <;>
    simp only [compileMu, first, second, unsupported, OrdinaryWork, implies_true]

/-- Original reference lookup emits only recursive requests and pure continuations. -/
theorem compileReference_ordinaryWork [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) : OrdinaryWork (compileReference domain name other left) := by
  by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · simp only [compileReference, member, ite_true, OrdinaryWork]
    intro found
    cases found with
    | none => trivial
    | some bound => cases left <;> simp only [Bool.false_eq_true, ite_false, ite_true, requestNode, OrdinaryWork, implies_true]
  · simp only [compileReference, member, ite_false, OrdinaryWork]

/-- Every compiled edge job retains all existing Mu records. -/
theorem compileEdge_ordinaryWork [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : EdgeRequest Symbol Guard) : OrdinaryWork (compileEdge emptyGuard conjoin request) := by
  have edgeWork (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) :
      OrdinaryWork (.work (makeEdge symbol guard values) (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))) :=
    ⟨by intro state key entry body depth ordinary stored; exact stored, fun _ => trivial⟩
  unfold compileEdge
  split
  · apply ordinaryWork_bind
    · exact ordinaryWork_walk _ _ (fun _ _ => by intro value; trivial)
    · intro values
      exact edgeWork _ _ values
  · exact edgeWork _ _ [.empty]

/-- Row joining emits recursive edge requests and an ordinary node job. -/
theorem compileRows_ordinaryWork [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) : OrdinaryWork (compileRows domain left right) := by
  apply ordinaryWork_bind
  · exact ordinaryWork_walk _ _ (fun _ _ => by intro value; trivial)
  · intro values
    exact ⟨InternedShallowHeap.makeNode_noNewMu values, fun _ => trivial⟩

/-- Every actual source node branch has only ordinary work jobs outside its explicit optional binders. -/
theorem compileNode_ordinaryWork [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (request : NodeRequest Symbol Guard) :
    OrdinaryWork (compileNode request) := by
  cases selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right with
  | empty | reset | self | swap | repeated key | unsupported =>
      simp only [compileNode, selected, unsupported, requestNode, OrdinaryWork, implies_true]
  | bothMu | leftMu | rightMu => simpa only [compileNode, selected] using compileMu_ordinaryWork request.domain request.left request.right
  | leftUnion =>
      simp only [compileNode, selected]
      cases request.left with
      | union entry members depth free =>
          apply ordinaryWork_bind
          · exact ordinaryWork_walk _ _ (fun _ _ => by intro value; trivial)
          · intro values
            exact ⟨InternedShallowHeap.makeUnion_noNewMu values, fun _ => trivial⟩
      | empty | reference | node | mu => trivial
  | rightUnion =>
      simp only [compileNode, selected]
      cases request.right with
      | union entry members depth free =>
          apply ordinaryWork_bind
          · exact ordinaryWork_walk _ _ (fun _ _ => by intro value; trivial)
          · intro values
            exact ⟨InternedShallowHeap.makeUnion_noNewMu values, fun _ => trivial⟩
      | empty | reference | node | mu => trivial
  | leftReference =>
      simp only [compileNode, selected]
      cases request.left <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_ordinaryWork _ _ _ _ | trivial
  | rightReference =>
      simp only [compileNode, selected]
      cases request.right <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_ordinaryWork _ _ _ _ | trivial
  | ordinary =>
      simp only [compileNode, selected]
      cases request.left <;> cases request.right <;> first | exact compileRows_ordinaryWork _ _ _ | trivial

end MicroCFTA.SourceRecursiveIntersectionCode
