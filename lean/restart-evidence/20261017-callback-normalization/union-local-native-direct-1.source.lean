import MicroCFTA.SourceCurrentRequiredUnionNormalNative
import MicroCFTA.SourceCurrentNativeGuardCode

/-!
# Normal union writes in the complete checked native compiler

Each compiler branch derives its own constructor-write certificate.
The bounded checked interpreter retains union normality on every outcome.
The final request theorem needs no reached physical checks or result law.
-/
namespace MicroCFTA.SourceCurrentUnionNormalNativePrograms
open Cache InternedConstructorTemplates
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

private def WorkSafe [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard A) : Prop :=
  ∀ state, UnionNormal state → UnionNormal (run job state).2

private def Safe [DecidableEq (EdgeKey Symbol Guard)] : Code Symbol Guard A → Prop
  | .pure _ | .fail _ => True
  | .work job next => WorkSafe job ∧ ∀ value, Safe (next value)
  | .enter _ _ _ _ _ next | .read _ next | .optionalBinder _ _ next | .node _ next | .edge _ next =>
      ∀ value, Safe (next value)
  | .finishNode _ _ next | .finishEdge _ _ next => Safe next

private theorem safe_bind [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A)
    (next : A → Code Symbol Guard B) (safe : Safe code) (later : ∀ value, Safe (next value)) :
    Safe (code.bind next) := by
  induction code with
  | pure value => exact later value
  | fail => trivial
  | work job resume ih => exact ⟨safe.1,fun value => ih value (safe.2 value)⟩
  | enter domain left right first second resume ih | read name resume ih | optionalBinder pair body resume ih
    | node request resume ih | edge request resume ih => exact fun value => ih value (safe value)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih safe

private theorem safe_walk [DecidableEq (EdgeKey Symbol Guard)] (call : A → Code Symbol Guard B)
    (values : List A) (safe : ∀ value ∈ values, Safe (call value)) :
    Safe (SourceRecursiveIntersectionCode.walk call values) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      exact safe_bind _ _ (safe first List.mem_cons_self) (fun _ =>
        safe_bind _ _ (ih (fun value member => safe value (List.mem_cons_of_mem _ member))) (fun _ => trivial))

private theorem compileNode_safe [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (request : NodeRequest Symbol Guard) :
    Safe (compileNode request) := by
  have node : ∀ edges : List (EdgeValue Symbol Guard), Safe (.work (makeNode edges) .pure) :=
    fun edges => ⟨(fun state normal => SourceCurrentRequiredUnionNormal.node edges state normal), fun _ => trivial⟩
  have union : ∀ values : List (Value Symbol Guard), Safe (.work (makeUnion values) .pure) :=
    fun values => ⟨(fun state normal => SourceCurrentRequiredUnionNormal.union values state normal), fun _ => trivial⟩
  have mu : Safe (compileMu request.domain request.left request.right) := by
    unfold compileMu
    split <;> simp only [Fields, unsupported, implies_true]
  have reference : ∀ name other left, Safe (compileReference request.domain name other left) := by
    intro name other left
    unfold compileReference
    split
    · intro found
      cases found with
      | none => trivial
      | some bound => split <;> intro value <;> trivial
    · trivial
  have rows : ∀ left right, Safe (compileRows request.domain left right) := by
    intro left right
    exact safe_bind _ _ (safe_walk _ _ (fun _ _ => by intro value; trivial)) node
  cases selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right with
  | empty | reset | self | swap | repeated key | unsupported =>
      simp only [compileNode, selected, unsupported, requestNode, Fields, implies_true]
  | bothMu | leftMu | rightMu => simpa only [compileNode, selected] using mu
  | leftUnion =>
      simp only [compileNode, selected]
      cases request.left with
      | union entry members depth free => exact safe_bind _ _ (safe_walk _ _ (fun _ _ => by intro value; trivial)) union
      | empty | reference | node | mu => trivial
  | rightUnion =>
      simp only [compileNode, selected]
      cases request.right with
      | union entry members depth free => exact safe_bind _ _ (safe_walk _ _ (fun _ _ => by intro value; trivial)) union
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


private theorem sentinel_safe [DecidableEq (EdgeKey Symbol Guard)] (left : EdgeValue Symbol Guard) :
    Safe (SourceEqualityNativeCheckedCode.sentinel left) :=
  ⟨fun state normal => SourceCurrentRequiredUnionNormal.edge _ _ _ state normal,fun _ => trivial⟩

private theorem children_safe [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (left right : EdgeValue Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) :
    Safe (SourceEqualityNativeCheckedCode.children domain left right combined) :=
  safe_bind _ _ (safe_walk _ _ (fun _ _ => by intro value; trivial))
    (fun _ => ⟨fun state normal => SourceCurrentRequiredUnionNormal.edge _ _ _ state normal,fun _ => trivial⟩)

private def ControlSafe [DecidableEq (EdgeKey Symbol Guard)] : Control A → Prop
  | .code code => Safe code
  | .edgeBody _ next => ∀ value, Safe (next value)

private theorem body_safe [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before after : Checked width) (rest : Control A) (later : ∀ value, Safe (next value))
    (one : body request next before = .yielded rest after) : ControlSafe rest := by
  unfold body at one
  split at one
  · simp only [sentinel] at one
    cases one
    exact safe_bind _ _ (sentinel_safe _) later
  · split at one
    · cases one
    · cases one
    · split at one
      · cases one
      · cases one
      · split at one
        · cases one
        · simp only [sentinel] at one; cases one
          exact safe_bind _ _ (sentinel_safe _) later
        · simp only [sentinel] at one; cases one
          exact safe_bind _ _ (sentinel_safe _) later
        · cases one
          exact safe_bind _ _ (children_safe _ _ _ _) later

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

private theorem step_normal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (before : Checked width) (safe : ControlSafe control)
    (normal : UnionNormal before.native.machine.heap) :
    UnionNormal (step control before).state.native.machine.heap := by
  cases control with
  | edgeBody => rw [step,SourceEqualityNativeDemandOperations.body_native]; exact normal
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact normal
      | work job next => exact safe.1 _ normal
      | optionalBinder pair body next =>
          have retained := SourceCurrentRequiredUnionNormalNative.optional pair body before.native.machine.heap normal
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap <;>
            simpa only [step,SourceRecursiveIntersectionNative.step,actual,lift,SourceEqualityNativeDemand.Outcome.state,
              SourceRecursiveIntersectionThunks.advance,InternedNestedConstruction.Outcome.state] using retained
      | node request next =>
          change UnionNormal (lift before.operations (SourceRecursiveIntersectionNative.step
            SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin (.node request next) before.native)).state.native.machine.heap
          rw [lift_heap,SourceRecursiveIntersectionNative.node_step_machine]
          exact normal
      | edge request next => rw [SourceEqualityNativeDemandHeap.step_edge_heap]; exact normal

private theorem yielded_safe [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control rest : Control A) (before after : Checked width) (safe : ControlSafe control)
    (one : step control before = .yielded rest after) : ControlSafe rest := by
  cases control with
  | edgeBody request next => exact body_safe request next before after rest safe one
  | code code =>
      cases code with
      | pure | fail => cases one
      | work job next => cases one; exact safe.2 _
      | enter domain left right first second next | read name next => cases one; exact safe _
      | optionalBinder pair body next =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap <;>
            simp only [step,SourceRecursiveIntersectionNative.step,actual,lift] at one
          · cases one; exact safe _
          · cases one
      | finishNode handle value next | finishEdge handle value next => cases one; exact safe
      | node request next =>
          unfold step SourceRecursiveIntersectionNative.step at one
          rcases selected : lookupNode width request before.native with ⟨selection,chosen⟩
          rw [selected] at one
          cases selection with
          | direct actual =>
              simp only [lift] at one
              cases one
              exact safe_bind _ _ (compileNode_safe _) safe
          | memoized handle =>
              rcases demanded : demandNode handle chosen with ⟨action,running⟩
              rw [demanded] at one
              cases action with
              | absent | busy => cases one
              | ready value => cases one; exact safe value
              | evaluate actual =>
                  cases one
                  exact safe_bind _ _ (compileNode_safe _) (fun value => safe value)
      | edge request next =>
          unfold step at one
          rcases selected : lookupEdge width request before.native with ⟨handle,chosen⟩
          rw [selected] at one
          rcases demanded : demandEdge handle chosen with ⟨action,running⟩
          rw [demanded] at one
          cases action with
          | absent | busy => cases one
          | ready value => cases one; exact safe value
          | evaluate actual => cases one; exact fun value => safe value

/-- Every actual bounded checked node request retains union normality without future physical checks. -/
theorem request [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (left right : Value Symbol Guard)
    (before : Checked width) (normal : UnionNormal before.native.machine.heap) :
    UnionNormal (execute fuel (.code (requestNode domain left right)) before).state.native.machine.heap := by
  have all : ∀ fuel (control : Control (Value Symbol Guard)) (before : Checked width), ControlSafe control →
      UnionNormal before.native.machine.heap → UnionNormal (execute fuel control before).state.native.machine.heap := by
    intro count
    induction count with
    | zero => intro control before _ normal; exact normal
    | succ count ih =>
        intro control before safe normal
        have retained := step_normal control before safe normal
        cases one : step control before with
        | yielded rest after =>
            simpa only [execute,one] using ih rest after (yielded_safe control rest before after safe one)
              (by simpa only [one,SourceEqualityNativeDemand.Outcome.state] using retained)
        | done | failed | constraintError | blocked => simpa only [execute,one,SourceEqualityNativeDemand.Outcome.state] using retained
  exact all fuel _ before (by intro value; trivial) normal
end MicroCFTA.SourceCurrentUnionNormalNativePrograms
