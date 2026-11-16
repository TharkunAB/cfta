import MicroCFTA.SourceCurrentAllocatedNativeEmptyRootDomainAncestry
import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
import MicroCFTA.MergedColdReaderClosed

namespace MicroCFTA.SourceCurrentAllocatedNativeSourceEmptyEnterOperands
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat} {A B : Type}
set_option autoImplicit false

private def NodeClosed (request : NodeRequest Symbol Guard) : Prop :=
  request.domain.key = IntersectionEmptyDomain.emptyKey → request.left.free = [] ∧ request.right.free = []

private def EdgeClosed (request : EdgeRequest Symbol Guard) : Prop :=
  request.domain.key = IntersectionEmptyDomain.emptyKey →
    (∀ child ∈ request.left.children, child.free = []) ∧
    (∀ child ∈ request.right.children, child.free = [])

private def CodeClosed : Code Symbol Guard A → Prop
  | .pure _ | .fail _ => True
  | .work _ next | .read _ next | .optionalBinder _ _ next => ∀ value, CodeClosed (next value)
  | .node request next => NodeClosed request ∧ ∀ value, CodeClosed (next value)
  | .edge request next => EdgeClosed request ∧ ∀ value, CodeClosed (next value)
  | .enter domain left right first second next =>
      (domain.key = IntersectionEmptyDomain.emptyKey → left.free = [] ∧ right.free = []) ∧
      identity left = some first ∧ identity right = some second ∧
        ∀ (entered : Interned DomainKey), entered.key ≠ IntersectionEmptyDomain.emptyKey → CodeClosed (next entered)
  | .finishNode _ _ next | .finishEdge _ _ next => CodeClosed next

private def ControlClosed : Control A → Prop
  | .code code => CodeClosed code
  | .edgeBody request next => EdgeClosed request ∧ ∀ value, CodeClosed (next value)

private theorem closed_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (original : CodeClosed code) (continuation : ∀ value, CodeClosed (next value)) :
    CodeClosed (code.bind next) := by
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
      refine ⟨original.1, original.2.1, original.2.2.1, ?_⟩
      intro entered nonempty
      exact ih entered (original.2.2.2 entered nonempty)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih original

private theorem closed_walk (call : A → Code Symbol Guard B) (values : List A)
    (calls : ∀ value ∈ values, CodeClosed (call value)) : CodeClosed (walk call values) := by
  induction values with
  | nil => trivial
  | cons first rest ih =>
      apply closed_bind _ _ (calls first List.mem_cons_self)
      intro value
      apply closed_bind _ _ (ih (fun member present => calls member (List.mem_cons_of_mem _ present)))
      intro values
      trivial

private theorem reset_closed (domain : DomainKey) (left right : Value Symbol Guard)
    (selected : decision domain left right = .reset) : left.free = [] ∧ right.free = [] := by
  have payloadApart : payload left right ≠ .reset := by
    cases left <;> cases right <;> intro same <;> cases same
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · rename_i restart
      constructor
      · cases free : left.free <;> simp_all [SourceRecursiveIntersectionControl.reset]
      · cases free : right.free <;> simp_all [SourceRecursiveIntersectionControl.reset]
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · split at selected
          · split at selected
            · cases selected
            · exact False.elim (payloadApart selected)
          · cases selected

private theorem mu_closed (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (closed : domain.key = IntersectionEmptyDomain.emptyKey → left.free = [] ∧ right.free = []) :
    CodeClosed (compileMu domain left right) := by
  unfold compileMu
  cases leftId : identity left with
  | none => trivial
  | some first =>
      cases rightId : identity right with
      | none => trivial
      | some second =>
          simp only [CodeClosed]
          refine ⟨closed, leftId, rightId, ?_⟩
          intro entered nonempty
          refine ⟨?_, fun _ _ => trivial⟩
          intro empty
          exact False.elim (nonempty empty)

private theorem reference_closed (domain : Interned DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) : CodeClosed (compileReference domain name other left) := by
  by_cases member : name ∈ names domain.key
  · simp only [compileReference, member, ite_true, CodeClosed]
    intro found
    cases found with
    | none => trivial
    | some bound =>
        have domainNonempty : domain.key ≠ IntersectionEmptyDomain.emptyKey := by
          intro empty
          rw [empty] at member
          cases member
        cases left <;> simp only [Bool.false_eq_true, ite_false, ite_true, requestNode, CodeClosed]
        all_goals exact ⟨fun empty => False.elim (domainNonempty empty), fun _ => trivial⟩
  · simp only [compileReference, member, ite_false, CodeClosed]

private theorem rows_closed [DecidableEq Symbol] (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard))
    (closed : domain.key = IntersectionEmptyDomain.emptyKey →
      MergedColdReaderClosedInputs.ClosedEdges left ∧ MergedColdReaderClosedInputs.ClosedEdges right) :
    CodeClosed (compileRows domain left right) := by
  apply closed_bind
  · apply closed_walk
    intro rows member
    refine ⟨?_, fun _ => trivial⟩
    intro empty
    obtain ⟨leftMember, rightMember, _⟩ := (pairs_member left right rows).mp member
    exact ⟨(closed empty).1 rows.1 leftMember, (closed empty).2 rows.2 rightMember⟩
  · intro values value
    trivial

private theorem node_edges_closed (heap : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts heap) (parent : Value Symbol Guard) (available : Available heap parent)
    (closed : parent.free = []) : MergedColdReaderClosedInputs.ClosedEdges (InternedEdgeResidency.nodeEdges parent) := by
  cases parent with
  | node entry rows depth free => exact MergedColdReaderClosed.node_children_closed heap facts entry rows depth free available closed
  | empty | reference | union | mu => intro edge member; cases member

private theorem node_closed [DecidableEq Symbol] (heap : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts heap) (request : NodeRequest Symbol Guard)
    (leftAvailable : Available heap request.left) (rightAvailable : Available heap request.right)
    (closed : NodeClosed request) : CodeClosed (compileNode request) := by
  have edgesClosed : request.domain.key = IntersectionEmptyDomain.emptyKey →
      MergedColdReaderClosedInputs.ClosedEdges (InternedEdgeResidency.nodeEdges request.left) ∧
      MergedColdReaderClosedInputs.ClosedEdges (InternedEdgeResidency.nodeEdges request.right) := by
    intro empty
    exact ⟨node_edges_closed heap facts request.left leftAvailable (closed empty).1,
      node_edges_closed heap facts request.right rightAvailable (closed empty).2⟩
  cases selected : decision request.domain.key request.left request.right with
  | empty | self | repeated key | unsupported =>
      simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, CodeClosed]
  | reset =>
      simp only [compileNode, selected]
      exact ⟨fun _ => reset_closed _ _ _ selected, fun _ => trivial⟩
  | swap =>
      simp only [compileNode, selected]
      exact ⟨fun empty => ⟨(closed empty).2, (closed empty).1⟩, fun _ => trivial⟩
  | bothMu | leftMu | rightMu =>
      simpa only [compileNode, selected] using mu_closed request.domain request.left request.right closed
  | leftUnion =>
      simp only [compileNode, selected]
      cases leftShape : request.left with
      | union entry members depth free =>
          apply closed_bind
          · apply closed_walk
            intro member present
            refine ⟨?_, fun _ => trivial⟩
            intro empty
            have each := MergedColdReaderClosed.union_members_closed heap facts entry members depth free
              (by simpa only [leftShape] using leftAvailable)
              (by simpa only [leftShape, Value.free] using (closed empty).1)
            exact ⟨each member present, (closed empty).2⟩
          · intro values value
            trivial
      | empty | reference | node | mu => trivial
  | rightUnion =>
      simp only [compileNode, selected]
      cases rightShape : request.right with
      | union entry members depth free =>
          apply closed_bind
          · apply closed_walk
            intro member present
            refine ⟨?_, fun _ => trivial⟩
            intro empty
            have each := MergedColdReaderClosed.union_members_closed heap facts entry members depth free
              (by simpa only [rightShape] using rightAvailable)
              (by simpa only [rightShape, Value.free] using (closed empty).2)
            exact ⟨(closed empty).1, each member present⟩
          · intro values value
            trivial
      | empty | reference | node | mu => trivial
  | leftReference =>
      simp only [compileNode, selected]
      cases request.left <;> try trivial
      rename_i name
      cases name <;> first | exact reference_closed _ _ _ _ | trivial
  | rightReference =>
      simp only [compileNode, selected]
      cases request.right <;> try trivial
      rename_i name
      cases name <;> first | exact reference_closed _ _ _ _ | trivial
  | ordinary =>
      simp only [compileNode, selected]
      cases leftShape : request.left <;> cases rightShape : request.right <;>
        simp only [leftShape, rightShape, InternedEdgeResidency.nodeEdges] at edgesClosed
      all_goals first | exact rows_closed _ _ _ edgesClosed | trivial

private theorem sentinel_closed (left : EdgeValue Symbol Guard) :
    CodeClosed (SourceEqualityNativeCheckedCode.sentinel left) := by intro value; trivial

private theorem children_closed (request : EdgeRequest Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) (closed : EdgeClosed request) :
    CodeClosed (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) := by
  apply closed_bind
  · apply closed_walk
    intro children member
    refine ⟨?_, fun _ => trivial⟩
    intro empty
    have included := List.of_mem_zip member
    exact ⟨(closed empty).1 children.1 included.1, (closed empty).2 children.2 included.2⟩
  · intro values value
    trivial

private theorem body_closed (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (state after : Checked width)
    (rest : Control A) (one : SourceEqualityNativeDemand.body request next state = .yielded rest after)
    (original : EdgeClosed request ∧ ∀ value, CodeClosed (next value)) : ControlClosed rest := by
  unfold SourceEqualityNativeDemand.body at one
  split at one
  · cases one
    exact closed_bind _ _ (sentinel_closed _) original.2
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
          exact closed_bind _ _ (sentinel_closed _) original.2
        · cases one
          exact closed_bind _ _ (sentinel_closed _) original.2
        · cases one
          exact closed_bind _ _ (children_closed _ _ original.1) original.2

private theorem step_closed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control rest : Control A) (before after : Checked width)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (inputs : Inputs control before) (one : step control before = .yielded rest after)
    (original : ControlClosed control) : ControlClosed rest := by
  cases control with
  | edgeBody request next => exact body_closed request next before after rest one original
  | code code =>
      change CodeClosed code at original
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
          apply original.2.2.2
          intro empty
          have member : pair first second ∈
              (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
                domain.key left right first second).1.key.seen := by
            rw [SourceRecursiveIntersectionSchedule.entered_key _ physical.machine.2]
            exact (extend_seen _ _ _ _).mpr (Or.inl rfl)
          rw [empty] at member
          cases member
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
                  exact closed_bind _ _ (node_closed before.native.machine.heap physical.machine.1 request
                    inputs.1.2.1 inputs.1.2.2 original.1) original.2
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
                          exact closed_bind _ _ (node_closed before.native.machine.heap physical.machine.1 request
                    inputs.1.2.1 inputs.1.2.2 original.1) (fun value => original.2 value)
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

private theorem trace_closed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {count : Nat} {control rest : Control A} {before after : Checked width}
    (actual : Trace count control before rest after)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (original : ControlClosed control) : ControlClosed rest := by
  induction actual with
  | refl => exact original
  | cons control state next reached final result count inputs one tail ih =>
      have reachedPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid reached.native := by
        simpa only [one, Outcome.state] using
          SourceCurrentAllocatedNativePhysicalExecution.step_valid control state physical inputs
      exact ih reachedPhysical (step_closed control next state reached physical inputs one original)

/-- Actual stored dispatch inputs give closed operands at an earlier empty-parent enter. -/
theorem stored_dispatch_enter_closed_operands
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (caller : Caller width) (cached : EnumerationExpandableIndex.Cached Symbol Guard)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller cached)
    (source target sourceHandle targetHandle : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (sourceStored : cached.core.values[source]? =
      some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : cached.core.values[target]? =
      some (.unenumerated (some targetHandle) targetScs))
    (rootRequest : NodeRequest Symbol Guard)
    (rootEmpty : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (sourceDecoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap sourceHandle = some rootRequest.left)
    (targetDecoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap targetHandle = some rootRequest.right)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid caller.checked.native)
    (used : Nat) (after : Checked width) (parent : Interned DomainKey)
    (left right : Value Symbol Guard) (first second uid patternId : Nat)
    (next : Interned DomainKey → Code Symbol Guard (Value Symbol Guard))
    (actual : Trace used (.code (.node rootRequest .pure)) caller.checked
      (.code (.enter parent left right first second next)) after)
    (sameKey :
      (SourceRecursiveIntersectionEnvironment.enter after.native.machine.domains
        parent.key left right first second).1.key =
      SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey [uid]
        (SourceRecursiveIntersectionControl.pair uid patternId)) :
    parent.key = IntersectionEmptyDomain.emptyKey ∧ left.free = [] ∧ right.free = [] ∧
      ((SourceRecursiveIntersectionControl.identity left = some uid ∧
        SourceRecursiveIntersectionControl.identity right = some patternId) ∨
       (SourceRecursiveIntersectionControl.identity left = some patternId ∧
        SourceRecursiveIntersectionControl.identity right = some uid)) := by
  obtain ⟨_, _, _, realized, _, _⟩ := valid
  obtain ⟨sourceValue, sourceRead, _sourceAvailable, sourceClosed⟩ :=
    realized source sourceHandle sourceScs sourceStored
  obtain ⟨targetValue, targetRead, _targetAvailable, targetClosed⟩ :=
    realized target targetHandle targetScs targetStored
  have sourceSame : sourceValue = rootRequest.left := Option.some.inj (sourceRead.symm.trans sourceDecoded)
  have targetSame : targetValue = rootRequest.right := Option.some.inj (targetRead.symm.trans targetDecoded)
  have rootClosed : rootRequest.left.free = [] ∧ rootRequest.right.free = [] := by
    exact ⟨by simpa only [sourceSame] using sourceClosed, by simpa only [targetSame] using targetClosed⟩
  have initial : ControlClosed (.code (.node rootRequest .pure)) :=
    ⟨fun _ => rootClosed, fun _ => trivial⟩
  have reached := trace_closed actual physical initial
  change (parent.key = IntersectionEmptyDomain.emptyKey → left.free = [] ∧ right.free = []) ∧
    identity left = some first ∧ identity right = some second ∧
      (∀ (entered : Interned DomainKey), entered.key ≠ IntersectionEmptyDomain.emptyKey → CodeClosed (next entered)) at reached
  obtain ⟨parentEmpty, pairSame⟩ :=
    SourceCurrentAllocatedNativeEmptyRootDomainAncestry.empty_root_singleton_enter_parent
      rootRequest caller.checked after physical rootEmpty used parent left right first second uid patternId next actual sameKey
  have ordered : (first = uid ∧ second = patternId) ∨ (first = patternId ∧ second = uid) := by
    simp only [pair, Prod.mk.injEq] at pairSame
    omega
  refine ⟨parentEmpty, (reached.1 parentEmpty).1, (reached.1 parentEmpty).2, ?_⟩
  rcases ordered with ⟨firstSame, secondSame⟩ | ⟨firstSame, secondSame⟩
  · exact Or.inl ⟨reached.2.1.trans (congrArg some firstSame), reached.2.2.1.trans (congrArg some secondSame)⟩
  · exact Or.inr ⟨reached.2.1.trans (congrArg some firstSame), reached.2.2.1.trans (congrArg some secondSame)⟩

end MicroCFTA.SourceCurrentAllocatedNativeSourceEmptyEnterOperands
