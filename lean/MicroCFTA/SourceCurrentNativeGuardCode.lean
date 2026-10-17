import MicroCFTA.SourceCurrentAllocatedNativeCodeFields
import MicroCFTA.SourceEqualityNativeDemandBodyYield
import MicroCFTA.SourceEqualityNativeDemandOperations
import MicroCFTA.SourceEqualityNativeDemandAcceptedLanguage

/-!
# Guard predicates in actual native continuations

Static constructor requests retain their literal guards. Node compilation
emits no new guard. Actual checked edge bodies emit only source top or the
conjunction of their two current resident row guards.
-/
namespace MicroCFTA.SourceCurrentNativeGuardCode
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Every literal edge instruction satisfies the supplied guard predicate. -/
def Fields (valid : Guard → Prop) : Code Symbol Guard A → Prop
  | .pure _ | .fail _ => True
  | .work job next => SourceEqualityAnnotationHeap.SafeWork valid job ∧ ∀ value, Fields valid (next value)
  | .enter _ _ _ _ _ next => ∀ value, Fields valid (next value)
  | .read _ next => ∀ value, Fields valid (next value)
  | .optionalBinder _ _ next => ∀ value, Fields valid (next value)
  | .node _ next => ∀ value, Fields valid (next value)
  | .edge _ next => ∀ value, Fields valid (next value)
  | .finishNode _ _ next | .finishEdge _ _ next => Fields valid next

/-- A larger guard predicate retains every literal constructor check. -/
theorem work_mono (first last : Guard → Prop) (increase : ∀ guard, first guard → last guard)
    (job : Work Symbol Guard A) (fields : SourceEqualityAnnotationHeap.SafeWork first job) :
    SourceEqualityAnnotationHeap.SafeWork last job := by
  induction job with
  | pure => trivial
  | edge key identify next ih => exact ⟨increase _ fields.1, fun value => ih value (fields.2 value)⟩
  | node key identify next ih => exact fun value => ih value (fields value)

/-- Widening the guard predicate retains every captured continuation. -/
theorem mono (first last : Guard → Prop) (increase : ∀ guard, first guard → last guard)
    (code : Code Symbol Guard A) (fields : Fields first code) : Fields last code := by
  induction code with
  | pure | fail => trivial
  | work job next ih => exact ⟨work_mono first last increase job fields.1, fun value => ih value (fields.2 value)⟩
  | enter domain left right firstId secondId next ih | read name next ih | optionalBinder pair body next ih
    | node request next ih | edge request next ih => exact fun value => ih value (fields value)
  | finishNode handle value next ih | finishEdge handle value next ih => exact ih fields

/-- Appended code retains the checks from both original continuations. -/
theorem bind (valid : Guard → Prop) (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (fields : Fields valid code) (later : ∀ value, Fields valid (next value)) : Fields valid (code.bind next) := by
  induction code with
  | pure value => exact later value
  | fail => trivial
  | work job resume ih => exact ⟨fields.1, fun value => ih value (fields.2 value)⟩
  | enter domain left right firstId secondId resume ih | read name resume ih | optionalBinder pair body resume ih
    | node request resume ih | edge request resume ih => exact fun value => ih value (fields value)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih fields

/-- An ordered walk retains the checks for its original calls. -/
theorem walk (valid : Guard → Prop) (call : A → Code Symbol Guard B) (values : List A)
    (calls : ∀ value ∈ values, Fields valid (call value)) :
    Fields valid (SourceRecursiveIntersectionCode.walk call values) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      apply bind valid _ _ (calls first List.mem_cons_self)
      intro value
      exact bind valid _ _ (ih (fun other member => calls other (List.mem_cons_of_mem _ member))) (fun _ => trivial)

/-- Native node compilation emits no literal edge guard in any source branch. -/
theorem compileNode_fields [DecidableEq Symbol] (valid : Guard → Prop) (request : NodeRequest Symbol Guard) :
    Fields valid (compileNode request) := by
  have node : ∀ edges : List (EdgeValue Symbol Guard), Fields valid (.work (makeNode edges) .pure) :=
    fun edges => ⟨SourceEqualityAnnotationHeap.makeNode valid edges, fun _ => trivial⟩
  have union : ∀ values : List (Value Symbol Guard), Fields valid (.work (makeUnion values) .pure) :=
    fun values => ⟨SourceEqualityAnnotationHeap.makeUnion valid values, fun _ => trivial⟩
  have mu : Fields valid (compileMu request.domain request.left request.right) := by
    unfold compileMu
    split <;> simp only [Fields, unsupported, implies_true]
  have reference : ∀ name other left, Fields valid (compileReference request.domain name other left) := by
    intro name other left
    unfold compileReference
    split
    · intro found
      cases found with
      | none => trivial
      | some bound => split <;> intro value <;> trivial
    · trivial
  have rows : ∀ left right, Fields valid (compileRows request.domain left right) := by
    intro left right
    exact bind valid _ _ (walk valid _ _ (fun _ _ => by intro value; trivial)) node
  cases selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right with
  | empty | reset | self | swap | repeated key | unsupported =>
      simp only [compileNode, selected, unsupported, requestNode, Fields, implies_true]
  | bothMu | leftMu | rightMu => simpa only [compileNode, selected] using mu
  | leftUnion =>
      simp only [compileNode, selected]
      cases request.left with
      | union entry members depth free => exact bind valid _ _ (walk valid _ _ (fun _ _ => by intro value; trivial)) union
      | empty | reference | node | mu => trivial
  | rightUnion =>
      simp only [compileNode, selected]
      cases request.right with
      | union entry members depth free => exact bind valid _ _ (walk valid _ _ (fun _ _ => by intro value; trivial)) union
      | empty | reference | node | mu => trivial
  | leftReference =>
      simp only [compileNode, selected]
      cases request.left <;> try trivial
      rename_i name
      cases name <;> first | exact reference _ _ _ | trivial
  | rightReference =>
      simp only [compileNode, selected]
      cases request.right <;> try trivial
      rename_i name
      cases name <;> first | exact reference _ _ _ | trivial
  | ordinary =>
      simp only [compileNode, selected]
      cases request.left <;> cases request.right <;> first | exact rows _ _ | trivial

/-- The rejected branch emits only its literal source top guard. -/
theorem sentinel_fields (valid : Guard → Prop) (left : EdgeValue Symbol Guard)
    (top : valid SourceEqualityConstraintConstructors.top) :
    Fields valid (SourceEqualityNativeCheckedCode.sentinel left) :=
  ⟨SourceEqualityAnnotationHeap.makeEdge valid _ _ _ top, fun _ => trivial⟩

/-- The accepted branch retains the actual allocated conjunction readback. -/
theorem children_fields (valid : Guard → Prop) (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : EdgeValue Symbol Guard) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (guard : valid (SourceEqualityConjoinAllocation.readback combined)) :
    Fields valid (SourceEqualityNativeCheckedCode.children domain left right combined) :=
  bind valid _ _ (walk valid _ _ (fun _ _ => by intro value; trivial))
    (fun _ => ⟨SourceEqualityAnnotationHeap.makeEdge valid _ _ _ guard, fun _ => trivial⟩)

/-- An actual checked body derives each emitted guard from its current resident input rows. -/
theorem body_fields (valid : Guard → Prop) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (before after : Checked width) (rest : Control A)
    (operations : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (cached : SourceEqualityNativeDemandOperations.Fields (.edgeBody request next))
    (top : valid SourceEqualityConstraintConstructors.top)
    (combined : valid (SourceEqualityPCSNativeEdge.conjoin request.left.entry.key.constraint request.right.entry.key.constraint))
    (later : ∀ value, Fields valid (next value))
    (one : body request next before = .yielded rest after) :
    ∃ code, rest = .code code ∧ Fields valid code := by
  by_cases arity : request.left.children.length = request.right.children.length
  · have matched : ¬request.left.children.length ≠ request.right.children.length := by omega
    simp only [body, ite_eq_right matched] at one
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [firstLoaded] at one; cases one
    | ok first =>
      cases first with
      | none => simp only [firstLoaded] at one; cases one
      | some first =>
        simp only [firstLoaded] at one
        cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
        | error message => simp only [secondLoaded] at one; cases one
        | ok second =>
          cases second with
          | none => simp only [secondLoaded] at one; cases one
          | some second =>
            simp only [secondLoaded] at one
            split at one
            · cases one
            · cases one; exact ⟨_, rfl, bind valid _ _ (sentinel_fields valid _ top) later⟩
            · cases one; exact ⟨_, rfl, bind valid _ _ (sentinel_fields valid _ top) later⟩
            · rename_i result checked
              have same := SourceEqualityNativeDemandAcceptedLanguage.ready_readback request before first second result
                operations cached.1 cached.2 arity firstLoaded secondLoaded checked
              cases one
              refine ⟨_, rfl, bind valid _ _ (children_fields valid _ _ _ result ?_) later⟩
              rw [same]
              exact combined
  · simp only [body, ite_eq_left arity, sentinel] at one
    cases one
    exact ⟨_, rfl, bind valid _ _ (sentinel_fields valid _ top) later⟩

end MicroCFTA.SourceCurrentNativeGuardCode
