import MicroCFTA.SourceCurrentAllocatedNativeNodeReturnOrigin
import MicroCFTA.SourceCurrentNativeOrderedOriginalEntry
import MicroCFTA.SourceEqualityNativeDemandBodyCode

namespace MicroCFTA.SourceCurrentAllocatedNativeEmptyRootDomainAncestry
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} {A B : Type}
set_option autoImplicit false

private def KeyOrigin (key : DomainKey) : Prop := key.seen = [] → key.free = []

private theorem empty_origin : KeyOrigin IntersectionEmptyDomain.emptyKey := by
  intro _
  rfl

private theorem extended_origin (key : DomainKey) (bound : List Nat) (enteredPair : Nat × Nat) :
    KeyOrigin (extend key bound enteredPair) := by
  intro empty
  have member := (extend_seen key bound enteredPair enteredPair).mpr (Or.inl rfl)
  rw [empty] at member
  cases member

private def CodeOrigin : Code Symbol Guard A → Prop
  | .pure _ | .fail _ => True
  | .work _ next | .read _ next | .optionalBinder _ _ next => ∀ value, CodeOrigin (next value)
  | .node request next => KeyOrigin request.domain.key ∧ ∀ value, CodeOrigin (next value)
  | .edge request next => KeyOrigin request.domain.key ∧ ∀ value, CodeOrigin (next value)
  | .enter domain _ _ first second next =>
      KeyOrigin domain.key ∧ pair first second ∉ domain.key.seen ∧
        ∀ entered, KeyOrigin entered.key → CodeOrigin (next entered)
  | .finishNode _ _ next | .finishEdge _ _ next => CodeOrigin next

private def ControlOrigin : Control A → Prop
  | .code code => CodeOrigin code
  | .edgeBody request next => KeyOrigin request.domain.key ∧ ∀ value, CodeOrigin (next value)

private theorem origin_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (original : CodeOrigin code) (continuation : ∀ value, CodeOrigin (next value)) :
    CodeOrigin (code.bind next) := by
  induction code with
  | pure value => exact continuation value
  | fail failure => trivial
  | work job resume ih | read name resume ih | optionalBinder key body resume ih =>
      intro value
      exact ih value (original value)
  | node request resume ih | edge request resume ih =>
      refine ⟨original.1, ?_⟩
      intro value
      exact ih value (original.2 value)
  | enter domain left right first second resume ih =>
      refine ⟨original.1, original.2.1, ?_⟩
      intro entered enteredOrigin
      exact ih entered (original.2.2 entered enteredOrigin)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih original

private theorem origin_walk (call : A → Code Symbol Guard B) (values : List A)
    (calls : ∀ value ∈ values, CodeOrigin (call value)) : CodeOrigin (walk call values) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      apply origin_bind _ _ (calls first List.mem_cons_self)
      intro value
      apply origin_bind _ _ (ih (fun member present => calls member (List.mem_cons_of_mem _ present)))
      intro values
      trivial

private theorem selected_mu_fresh (domain : DomainKey) (left right : Value Symbol Guard)
    (selected : decision domain left right = .bothMu ∨ decision domain left right = .leftMu ∨
      decision domain left right = .rightMu) :
    ∀ first second, identity left = some first → identity right = some second →
      pair first second ∉ domain.seen := by
  intro first second leftId rightId member
  rcases selected with selected | selected | selected
  all_goals
    unfold decision at selected
    simp only [leftId, rightId, member, ite_true] at selected
    split at selected
    · cases selected
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · split at selected <;> cases selected

private theorem mu_origin (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (domainOrigin : KeyOrigin domain.key)
    (fresh : ∀ first second, identity left = some first → identity right = some second →
      pair first second ∉ domain.key.seen) : CodeOrigin (compileMu domain left right) := by
  unfold compileMu
  cases leftId : identity left with
  | none => trivial
  | some first =>
      cases rightId : identity right with
      | none => trivial
      | some second =>
          simp only [CodeOrigin]
          refine ⟨domainOrigin, fresh first second leftId rightId, ?_⟩
          intro entered enteredOrigin
          exact ⟨enteredOrigin, fun _ _ => trivial⟩

private theorem reference_origin (domain : Interned DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (domainOrigin : KeyOrigin domain.key) :
    CodeOrigin (compileReference domain name other left) := by
  by_cases member : name ∈ names domain.key
  · simp only [compileReference, member, ite_true, CodeOrigin]
    intro found
    cases found with
    | none => trivial
    | some bound =>
        cases left <;> simp only [Bool.false_eq_true, ite_false, ite_true, requestNode, CodeOrigin]
        all_goals exact ⟨domainOrigin, fun _ => trivial⟩
  · simp only [compileReference, member, ite_false, CodeOrigin]

private theorem rows_origin [DecidableEq Symbol] (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (domainOrigin : KeyOrigin domain.key) :
    CodeOrigin (compileRows domain left right) := by
  apply origin_bind
  · exact origin_walk _ _ (fun _ _ => ⟨domainOrigin, fun _ => trivial⟩)
  · intro values value
    trivial

private theorem node_origin [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (domainOrigin : KeyOrigin request.domain.key) : CodeOrigin (compileNode request) := by
  cases selected : decision request.domain.key request.left request.right with
  | empty | self | repeated key | unsupported =>
      simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, CodeOrigin]
  | reset =>
      simp only [compileNode, selected]
      change CodeOrigin (requestNode IntersectionEmptyDomain.emptyDomain request.left request.right)
      exact ⟨empty_origin, fun _ => trivial⟩
  | swap =>
      simp only [compileNode, selected]
      change CodeOrigin (requestNode request.domain request.right request.left)
      exact ⟨domainOrigin, fun _ => trivial⟩
  | bothMu =>
      simpa only [compileNode, selected] using mu_origin request.domain request.left request.right
        domainOrigin (selected_mu_fresh _ _ _ (Or.inl selected))
  | leftMu =>
      simpa only [compileNode, selected] using mu_origin request.domain request.left request.right
        domainOrigin (selected_mu_fresh _ _ _ (Or.inr (Or.inl selected)))
  | rightMu =>
      simpa only [compileNode, selected] using mu_origin request.domain request.left request.right
        domainOrigin (selected_mu_fresh _ _ _ (Or.inr (Or.inr selected)))
  | leftUnion =>
      simp only [compileNode, selected]
      cases request.left with
      | union entry members depth free =>
          apply origin_bind
          · exact origin_walk _ _ (fun _ _ => ⟨domainOrigin, fun _ => trivial⟩)
          · intro values value
            trivial
      | empty | reference | node | mu => trivial
  | rightUnion =>
      simp only [compileNode, selected]
      cases request.right with
      | union entry members depth free =>
          apply origin_bind
          · exact origin_walk _ _ (fun _ _ => ⟨domainOrigin, fun _ => trivial⟩)
          · intro values value
            trivial
      | empty | reference | node | mu => trivial
  | leftReference =>
      simp only [compileNode, selected]
      cases request.left <;> try trivial
      rename_i name
      cases name <;> first | exact reference_origin _ _ _ _ domainOrigin | trivial
  | rightReference =>
      simp only [compileNode, selected]
      cases request.right <;> try trivial
      rename_i name
      cases name <;> first | exact reference_origin _ _ _ _ domainOrigin | trivial
  | ordinary =>
      simp only [compileNode, selected]
      cases request.left <;> cases request.right <;>
        first | exact rows_origin _ _ _ domainOrigin | trivial

private theorem sentinel_origin (left : EdgeValue Symbol Guard) :
    CodeOrigin (SourceEqualityNativeCheckedCode.sentinel left) := by intro value; trivial

private theorem children_origin (request : EdgeRequest Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (domainOrigin : KeyOrigin request.domain.key) :
    CodeOrigin (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) := by
  apply origin_bind
  · exact origin_walk _ _ (fun _ _ => ⟨domainOrigin, fun _ => trivial⟩)
  · intro values value
    trivial

private theorem body_origin (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (state after : Checked width)
    (rest : Control A) (one : SourceEqualityNativeDemand.body request next state = .yielded rest after)
    (original : KeyOrigin request.domain.key ∧ ∀ value, CodeOrigin (next value)) : ControlOrigin rest := by
  unfold SourceEqualityNativeDemand.body at one
  split at one
  · cases one
    exact origin_bind _ _ (sentinel_origin _) original.2
  · split at one
    · cases one
    · cases one
    · split at one
      · cases one
      · cases one
      · dsimp only at one
        split at one
        · cases one
        · cases one
          exact origin_bind _ _ (sentinel_origin _) original.2
        · cases one
          exact origin_bind _ _ (sentinel_origin _) original.2
        · cases one
          exact origin_bind _ _ (children_origin _ _ original.1) original.2

private theorem step_origin [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control rest : Control A) (before after : Checked width)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (inputs : Inputs control before) (one : step control before = .yielded rest after)
    (original : ControlOrigin control) : ControlOrigin rest := by
  cases control with
  | edgeBody request next => exact body_origin request next before after rest one original
  | code code =>
      change CodeOrigin code at original
      cases code with
      | pure value | fail failure =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
      | work job next =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact original _
      | enter domain left right first second next =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          apply original.2.2
          rw [SourceRecursiveIntersectionSchedule.entered_key _ physical.machine.2]
          exact extended_origin _ _ _
      | read name next =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact original _
      | optionalBinder key value next =>
          simp only [step, SourceRecursiveIntersectionNative.step] at one
          cases produced : SourceRecursiveIntersectionMaybeMu.maybeMu key value before.native.machine.heap with
          | done result heap =>
              simp only [produced, lift] at one
              cases one
              exact original result
          | pending pending heap => simp only [produced, lift] at one; cases one
      | finishNode handle value next | finishEdge handle value next =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact original
      | node request next =>
          simp only [step, SourceRecursiveIntersectionNative.step] at one
          cases selected : lookupNode width request before.native with
          | mk selection chosen =>
              cases selection with
              | direct actual =>
                  have same := (SourceRecursiveIntersectionNative.lookupNode_direct request actual before.native chosen selected).1
                  subst actual
                  simp only [selected, lift] at one
                  cases one
                  exact origin_bind _ _ (node_origin request original.1) original.2
              | memoized handle =>
                  obtain ⟨key, requested, _, _⟩ :=
                    SourceRecursiveIntersectionNative.lookupNode_memoized request before.native chosen handle selected
                  cases demanded : demandNode handle chosen with
                  | mk demand running =>
                      cases demand with
                      | absent | busy => simp only [selected, demanded, lift] at one; cases one
                      | ready value =>
                          simp only [selected, demanded, lift] at one
                          cases one
                          exact original.2 value
                      | evaluate actual =>
                          have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual
                            before.native chosen running handle physical inputs.1 (inputs.2 key requested) selected demanded
                          subst actual
                          simp only [selected, demanded, lift] at one
                          cases one
                          exact origin_bind _ _ (node_origin request original.1) (fun value => original.2 value)
      | edge request next =>
          simp only [step] at one
          cases selected : lookupEdge width request before.native with
          | mk handle chosen =>
              cases demanded : demandEdge handle chosen with
              | mk demand running =>
                  cases demand with
                  | absent | busy => simp only [selected, demanded] at one; cases one
                  | ready value =>
                      simp only [selected, demanded] at one
                      cases one
                      exact original.2 value
                  | evaluate actual =>
                      have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual
                        before.native chosen running handle physical inputs.1 inputs.2 selected demanded
                      subst actual
                      simp only [selected, demanded] at one
                      cases one
                      exact ⟨original.1, fun value => original.2 value⟩

private theorem trace_origin [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {count : Nat} {control rest : Control A} {before after : Checked width}
    (actual : Trace count control before rest after)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (original : ControlOrigin control) : ControlOrigin rest := by
  induction actual with
  | refl => exact original
  | cons control state next reached final result count inputs one tail ih =>
      have reachedPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid reached.native := by
        simpa only [one, Outcome.state] using
          SourceCurrentAllocatedNativePhysicalExecution.step_valid control state physical inputs
      exact ih reachedPhysical (step_origin control next state reached physical inputs one original)

/-- An actual singleton-key enter from an empty-domain root has an empty parent key. -/
theorem empty_root_singleton_enter_parent
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (rootRequest : NodeRequest Symbol Guard)
    (before after : Checked width)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (rootEmpty : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (used : Nat) (parent : Interned DomainKey)
    (left right : Value Symbol Guard) (first second uid patternId : Nat)
    (next : Interned DomainKey → Code Symbol Guard (Value Symbol Guard))
    (actual : Trace used (.code (.node rootRequest .pure)) before
      (.code (.enter parent left right first second next)) after)
    (sameKey :
      (SourceRecursiveIntersectionEnvironment.enter after.native.machine.domains
        parent.key left right first second).1.key =
      SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey [uid]
        (SourceRecursiveIntersectionControl.pair uid patternId)) :
    parent.key = IntersectionEmptyDomain.emptyKey ∧
      SourceRecursiveIntersectionControl.pair first second =
        SourceRecursiveIntersectionControl.pair uid patternId := by
  have rootOrigin : ControlOrigin (.code (.node rootRequest .pure)) := by
    refine ⟨?_, fun _ => trivial⟩
    rw [rootEmpty]
    exact empty_origin
  have reached := trace_origin actual physical rootOrigin
  change KeyOrigin parent.key ∧ pair first second ∉ parent.key.seen ∧
    (∀ entered, KeyOrigin entered.key → CodeOrigin (next entered)) at reached
  have reachedPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension actual physical).1
  have keyEquation := SourceRecursiveIntersectionSchedule.entered_key
    after.native.machine.domains reachedPhysical.machine.2 parent.key left right first second
  let bound := (SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst
  have enteredPair : pair first second ∈ (extend parent.key bound (pair first second)).seen :=
    (extend_seen parent.key bound (pair first second) (pair first second)).mpr (Or.inl rfl)
  have fullKey : extend parent.key bound (pair first second) =
      extend IntersectionEmptyDomain.emptyKey [uid] (pair uid patternId) := by
    exact keyEquation.symm.trans sameKey
  have onlyPair : ∀ candidate ∈ (extend parent.key bound (pair first second)).seen,
      candidate = pair uid patternId := by
    intro candidate member
    rw [fullKey] at member
    rcases (extend_seen IntersectionEmptyDomain.emptyKey [uid] (pair uid patternId) candidate).mp member with
      same | absent
    · exact same
    · cases absent
  have pairSame := onlyPair _ enteredPair
  have seenEmpty : parent.key.seen = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro candidate member
    have incoming := (extend_seen parent.key bound (pair first second) candidate).mpr (Or.inr member)
    have same := onlyPair candidate incoming
    apply reached.2.1
    rw [pairSame, ← same]
    exact member
  have freeEmpty := reached.1 seenEmpty
  have keySame : parent.key = DomainKey.mk [] parent.key.seen :=
    congrArg (fun free => DomainKey.mk free parent.key.seen) freeEmpty
  rw [seenEmpty] at keySame
  exact ⟨keySame, pairSame⟩

end MicroCFTA.SourceCurrentAllocatedNativeEmptyRootDomainAncestry
