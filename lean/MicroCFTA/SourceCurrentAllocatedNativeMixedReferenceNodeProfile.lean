import MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
import MicroCFTA.SourceCurrentAllocatedNativeFinitePrefixReferenceControl

/-!
# Original mixed reference queries against closed ordinary nodes

The original entry and producer share one actual checked trace.
The source read keeps the same original domain and full stored universe.
The opposite order swaps to the same original mixed request family.
Ready cells retain their exact original coupled law.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMixedReferenceNodeProfile
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisUniversePrefixHeight (height)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

private theorem through_head
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (fuel : Nat) (control : Control (Value Symbol Guard)) (state : Checked width)
    (plan : InputsThrough fuel control state) : Inputs control state := by
  cases fuel with
  | zero => exact plan
  | succ fuel => exact plan.1

private theorem one_step
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (control next : Control (Value Symbol Guard)) (before after : Checked width)
    (actual : Steps 1 control before next after) :
    SourceEqualityNativeDemand.step control before = .yielded next after := by
  obtain ⟨rest, middle, one, tail⟩ := steps_succ 0 _ _ _ _ actual
  obtain ⟨sameControl, sameState⟩ := steps_zero _ _ _ _ tail
  simpa only [sameControl, sameState] using one

private theorem node_step_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (before : Checked width)
    (nodes : Returned nodeLaw before.native.nodes) (edges : Returned edgeLaw before.native.edges) :
    Returned nodeLaw (step (.code (.node request .pure)) before).state.native.nodes ∧
      Returned edgeLaw (step (.code (.node request .pure)) before).state.native.edges := by
  have published : Returned nodeLaw (lookupNode width request before.native).2.nodes ∧
      Returned edgeLaw (lookupNode width request before.native).2.edges := by
    cases keyed : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
    | none => simpa only [lookupNode, keyed] using And.intro nodes edges
    | some physicalKey =>
        constructor
        · simpa only [lookupNode, keyed] using
            SourceCurrentAllocatedNativeContextCache.returned_lookup nodeLaw physicalKey request before.native.nodes nodes
        · simpa only [lookupNode, keyed] using edges
  cases selected : lookupNode width request before.native with
  | mk selection chosen =>
      have chosenNodes : Returned nodeLaw chosen.nodes := by
        simpa only [selected] using published.1
      have chosenEdges : Returned edgeLaw chosen.edges := by
        simpa only [selected] using published.2
      cases selection with
      | direct actual =>
          simpa only [step, SourceRecursiveIntersectionNative.step, selected, lift, Outcome.state] using
            And.intro chosenNodes chosenEdges
      | memoized handle =>
          have demandedNodes : Returned nodeLaw (demandNode handle chosen).2.nodes :=
            SourceCurrentAllocatedNativeContextCache.returned_demand nodeLaw handle chosen.nodes chosenNodes
          have demandedEdges : Returned edgeLaw (demandNode handle chosen).2.edges := chosenEdges
          cases demanded : demandNode handle chosen with
          | mk observation current =>
              have currentNodes : Returned nodeLaw current.nodes := by
                simpa only [demanded] using demandedNodes
              have currentEdges : Returned edgeLaw current.edges := by
                simpa only [demanded] using demandedEdges
              cases observation <;>
                simpa only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, Outcome.state] using
                  And.intro currentNodes currentEdges

/-- Both original mixed reference orders inherit Profile from genuine smaller same-domain closed or mixed queries. -/
theorem current_stored_universe_reference_node_profile_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {Output : Type}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (pattern : Node) (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId)
    (patternKind : tag pattern = 1 ∨ tag pattern = 3)
    (operand : Node) (operandEntry : Interned NodeKey)
    (operandRows : List (EdgeValue Symbol Guard)) (operandLevel : Nat)
    (operandShape : operand = .node operandEntry operandRows operandLevel [])
    (operandProfile : Profile entry.identity operand)
    (smaller : height operand < height pattern) (referenceFirst : Bool)
    (initial : Control Output) (start entryBefore before reader : Checked width)
    (startPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (wholeCount entryCount queryCount : Nat) (final : Control Output)
    (wholeActual : Trace wholeCount initial start final reader)
    (entryStrict : entryCount < wholeCount)
    (entryNext : Interned DomainKey → Code Symbol Guard Output)
    (entryPrefix : Steps entryCount initial start
      (.code (.enter IntersectionEmptyDomain.emptyDomain (.mu entry body depth ordinary)
        pattern entry.identity patternId entryNext)) entryBefore) :
    let universeValue : Node := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    let request : NodeRequest Symbol Guard := ⟨entered.1,
      if referenceFirst then .reference (.interned entry.identity) else operand,
      if referenceFirst then operand else .reference (.interned entry.identity)⟩
    ∀ (outerNext : Node → Code Symbol Guard Output),
    Steps queryCount initial start
      (.code ((requestNode request.domain request.left request.right).bind outerNext)) before →
    ∀ (remainder : NodeRequest Symbol Guard → Node → Prop)
      (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
      (parentFuel count : Nat) (value : Node) (after : Checked width),
    Physical before.native → Grows sourceHeap before.native.machine.heap →
    SourceEqualityConstraintMemoAllocation.Valid before.operations →
    InputsThrough parentFuel (.code (.node request .pure)) before →
    FieldsThrough parentFuel (.code (.node request .pure)) before →
    Returned (fun old result => (old = request → Profile entry.identity result) ∧ remainder old result)
      before.native.nodes → Returned edgeLaw before.native.edges →
    count ≤ parentFuel → queryCount + count ≤ wholeCount →
    Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
    (∀ (child : NodeRequest Symbol Guard) (used childFuel childCount : Nat),
      0 < used → childFuel < parentFuel → used + childFuel ≤ parentFuel →
      childCount ≤ childFuel → used + childCount ≤ count →
      ((child = ⟨entered.1, operand, universeValue⟩ ∧
          Profile entry.identity child.left ∧ Profile entry.identity child.right ∧
          child.domain.key.free.isEmpty = false) ∨
        child = ⟨entered.1, operand, .reference (.interned entry.identity)⟩) →
      ∀ (next : Node → Code Symbol Guard Node) (first middle : Checked width) (result : Node),
      Steps used (.code (.node request .pure)) before
        (.code ((requestNode child.domain child.left child.right).bind next)) first →
      Physical first.native → Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      InputsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      FieldsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      Returned (fun old result => (old = request → Profile entry.identity result) ∧ remainder old result)
        first.native.nodes → Returned edgeLaw first.native.edges →
      Available first.native.machine.heap child.left → Available first.native.machine.heap child.right →
      Steps childCount (.code (requestNode child.domain child.left child.right)) first
        (.code (.pure result)) middle → Profile entry.identity result) →
    Profile entry.identity value ∧ Available after.native.machine.heap value ∧ Physical after.native ∧
    Extension before.native.machine after.native.machine ∧ Grows sourceHeap after.native.machine.heap ∧
    SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations := by
  let universeValue : Node := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let request : NodeRequest Symbol Guard := ⟨entered.1,
    if referenceFirst then .reference (.interned entry.identity) else operand,
    if referenceFirst then operand else .reference (.interned entry.identity)⟩
  dsimp only
  intro outerNext queryPrefix remainder edgeLaw parentFuel count value after
    physical growth operationsValid plan fields nodes edges bounded inside actual children
  have current := through_head parentFuel (.code (.node request .pure)) before plan
  have operandAvailable : Available before.native.machine.heap operand := by
    cases referenceFirst with
    | false => exact current.1.2.1
    | true => exact current.1.2.2
  have prior : Returned (fun old result => old = request → Profile entry.identity result)
      before.native.nodes := by
    intro handle old result storedCell
    exact (nodes handle old result storedCell).1
  have observed : execute (count + 1) (.code (.node request .pure)) before = .done value after :=
    trace_done count _ before after value actual
  have profile : Profile entry.identity value := by
    have resultLaw := SourceCurrentAllocatedNativeNodeQueryResult.node_query_result_of_body_induction
      (fun old result => old = request → Profile entry.identity result)
      request before after (count + 1) value physical current.1 current.2 prior observed (by
        intro bodySteps bodyBound next first middle result origin bodyTrace
        intro _same
        have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
          parentFuel 1 (.code (.node request .pure)) (.code (compileNode request)) next
          before first sourceHeap physical plan fields operationsValid growth origin (by omega)
        obtain ⟨_checked, firstPhysical, firstExtension, firstGrowth, firstOperations,
          _operationsGrowth, _boundPlan, firstPlan, _boundFields, firstFields⟩ := reached
        have firstOperandAvailable : Available first.native.machine.heap operand :=
          firstExtension.available operand operandAvailable
        have lifted := origin.bind _ _ _ _ _ outerNext
        have composed := queryPrefix.trans _ _ _ _ _ _ _ _ lifted
        have bodyPrefix : Steps (queryCount + 1) initial start
            (.code ((compileNode request).bind (fun result => (next result).bind outerNext))) first := by
          simpa only [Control.bind, Code.bind_assoc] using composed
        have controlled :=
          SourceCurrentAllocatedNativeFinitePrefixReferenceControl.current_stored_universe_ref_control_at_finite_prefix
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            pattern patternClosed patternId patternIdentity patternKind initial start entryBefore first reader
            startPhysical sourceGrowth wholeCount entryCount (queryCount + 1) final wholeActual
            entryStrict (by omega) entryNext entryPrefix operand firstOperandAvailable operandProfile.1 smaller
            referenceFirst (fun result => (next result).bind outerNext) bodyPrefix
        obtain ⟨_entryBound, _producerBound, _entryChecked, _entrySuffix, _producerChecked, _producerSuffix,
          universeClosed, _universeAvailable, _readerExtension, bound, _lookup, _read,
          _referenceFresh, _operandFresh, controls⟩ := controlled
        obtain ⟨_ordinaryDecision, _swapDecision, _ordinaryCode, swapCode, ordinaryRead, _swapStep⟩ :=
          controls operandEntry operandRows operandLevel operandShape
        have universeProfile : Profile entry.identity universeValue := by
          refine ⟨universeClosed, ?_⟩
          intro atom member
          simpa only [universeValue, InternedBoundaryAtoms.atoms, List.mem_singleton] using member
        have nonempty : entered.1.key.free.isEmpty = false := by
          change entry.identity ∈ names entered.1.key at bound
          cases freeMap : entered.1.key.free with
          | nil => simp only [names, freeMap, List.map_nil, List.not_mem_nil] at bound
          | cons head tail => rfl
        have one := one_step (.code (.node request .pure))
          (.code ((compileNode request).bind next)) before first origin
        have firstLaws := node_step_returned
          (fun old result => (old = request → Profile entry.identity result) ∧ remainder old result)
          edgeLaw request before nodes edges
        have firstNodes : Returned
            (fun old result => (old = request → Profile entry.identity result) ∧ remainder old result)
            first.native.nodes := by
          simpa only [one, Outcome.state] using firstLaws.1
        have firstEdges : Returned edgeLaw first.native.edges := by
          simpa only [one, Outcome.state] using firstLaws.2
        cases referenceFirst with
        | false =>
            let child : NodeRequest Symbol Guard := ⟨entered.1, operand, universeValue⟩
            have reading : step (.code (compileNode request)) first =
                .yielded (.code (requestNode child.domain child.left child.right)) first := ordinaryRead
            cases bodySteps with
            | zero =>
                have same := (steps_zero _ _ _ _ bodyTrace).1
                rw [same] at reading
                cases reading
            | succ remaining =>
                obtain ⟨rest, reachedState, actualOne, tail⟩ := steps_succ remaining _ _ _ _ bodyTrace
                obtain ⟨sameControl, sameState⟩ := Outcome.yielded.inj (actualOne.symm.trans reading)
                have childTrace : Steps remaining
                    (.code (requestNode child.domain child.left child.right)) first
                    (.code (.pure result)) middle := by
                  simpa only [sameControl, sameState] using tail
                have readOrigin : Steps 1 (.code (compileNode request)) first
                    (.code (requestNode child.domain child.left child.right)) first :=
                  .cons _ _ _ _ _ _ _ reading (.refl _ _)
                have appended := readOrigin.bind _ _ _ _ _ next
                have joined := origin.trans _ _ _ _ _ _ _ _ appended
                have childOrigin : Steps 2 (.code (.node request .pure)) before
                    (.code ((requestNode child.domain child.left child.right).bind next)) first := by
                  change Steps 2 (.code (requestNode request.domain request.left request.right)) before
                    (.code ((requestNode child.domain child.left child.right).bind next)) first
                  simpa only [Control.bind] using joined
                have childReached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
                  parentFuel 2 (.code (.node request .pure))
                  (.code (requestNode child.domain child.left child.right)) next
                  before first sourceHeap physical plan fields operationsValid growth childOrigin (by omega)
                obtain ⟨_childChecked, childPhysical, _childExtension, childGrowth, childOperations,
                  _childOperationGrowth, _childBoundPlan, childPlan, _childBoundFields, childFields⟩ := childReached
                have childReady := through_head (parentFuel - 2)
                  (.code (requestNode child.domain child.left child.right)) first childPlan
                exact children child 2 (parentFuel - 2) remaining (by decide) (by omega) (by omega)
                  (by omega) (by omega) (.inl ⟨rfl, operandProfile, universeProfile, nonempty⟩)
                  next first middle result childOrigin childPhysical childGrowth childOperations
                  childPlan childFields firstNodes firstEdges childReady.1.2.1 childReady.1.2.2 childTrace
        | true =>
            let child : NodeRequest Symbol Guard :=
              ⟨entered.1, operand, .reference (.interned entry.identity)⟩
            have compiled : compileNode request = requestNode child.domain child.left child.right := swapCode
            have childOrigin : Steps 1 (.code (.node request .pure)) before
                (.code ((requestNode child.domain child.left child.right).bind next)) first := by
              change Steps 1 (.code (requestNode request.domain request.left request.right)) before
                (.code ((requestNode child.domain child.left child.right).bind next)) first
              simpa only [compiled] using origin
            have childTrace : Steps bodySteps (.code (requestNode child.domain child.left child.right)) first
                (.code (.pure result)) middle := by
              simpa only [compiled] using bodyTrace
            have childPlan : InputsThrough (parentFuel - 1)
                (.code (requestNode child.domain child.left child.right)) first := by
              simpa only [compiled] using firstPlan
            have childFields : FieldsThrough (parentFuel - 1)
                (.code (requestNode child.domain child.left child.right)) first := by
              simpa only [compiled] using firstFields
            have childReady := through_head (parentFuel - 1)
              (.code (requestNode child.domain child.left child.right)) first childPlan
            exact children child 1 (parentFuel - 1) bodySteps (by decide) (by omega) (by omega)
              (by omega) (by omega) (.inr rfl) next first middle result childOrigin
              firstPhysical firstGrowth firstOperations childPlan childFields firstNodes firstEdges
              childReady.1.2.1 childReady.1.2.2 childTrace)
    exact resultLaw rfl
  have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel count (.code (.node request .pure)) (.code (.pure value)) .pure
    before after sourceHeap physical plan fields operationsValid growth actual bounded
  obtain ⟨checked, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
    _boundPlan, _rawPlan, _boundFields, _rawFields⟩ := reached
  have available := SourceCurrentNativeOpenRequestResults.node_result
    count request before after value physical checked
  exact ⟨profile, available, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth⟩

end MicroCFTA.SourceCurrentAllocatedNativeMixedReferenceNodeProfile
