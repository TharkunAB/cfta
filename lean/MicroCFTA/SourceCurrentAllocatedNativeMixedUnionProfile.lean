import MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
import MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit
import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness
import MicroCFTA.SourceEqualityNativeDemandWalkExecution
import MicroCFTA.MergedColdReaderClosedInputs

namespace MicroCFTA.SourceCurrentAllocatedNativeMixedUnionProfile
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisUniversePrefixHeight (height)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand
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
    (fuel : Nat) (control : Control Node) (state : Checked width)
    (plan : InputsThrough fuel control state) : Inputs control state := by
  cases fuel with
  | zero => exact plan
  | succ fuel => exact plan.1

private theorem profiles_of_all_two {members values : List Node} (sourceName : Nat)
    (aligned : All₂ (fun _ value => Profile sourceName value) members values) :
    ∀ value ∈ values, Profile sourceName value := by
  induction aligned with
  | nil => intro value member; cases member
  | cons head tail ih =>
      intro value member
      cases member with
      | head => exact head
      | tail _ member => exact ih value member

private theorem physical_identity_apart_owner
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (entry : Interned NodeKey) (body depth ordinary : Node)
    (ownerAvailable : Available heap (.mu entry body depth ordinary))
    (value : Node) (available : Available heap value)
    (valueId : Nat) (valueIdentity : SourcePreparedSharedRows.reference value = some valueId)
    (different : value ≠ .mu entry body depth ordinary) : valueId ≠ entry.identity := by
  intro same
  have actualIdentity : SourcePreparedSharedRows.reference value = some entry.identity :=
    valueIdentity.trans (congrArg some same)
  have actualRead := SourcePreparedSharedRows.read_identity heap facts value available entry.identity actualIdentity
  have ownerRead := SourcePreparedSharedRows.read_identity heap facts
    (.mu entry body depth ordinary) ownerAvailable entry.identity rfl
  exact different (Option.some.inj (actualRead.symm.trans ownerRead))

private theorem pair_apart_owner (left right owner pattern : Nat)
    (leftApart : left ≠ owner) (rightApart : right ≠ owner) :
    pair left right ≠ pair owner pattern := by
  intro same
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair] at lower upper
  omega

private theorem body_union_branches
    (domain : Interned DomainKey) (ownerId : Nat)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (unionEntry : Interned NodeKey) (members : List Node) (level : Nat) (free : List Reference)
    (fresh : pair bodyEntry.identity unionEntry.identity ∉ domain.key.seen) :
    decision domain.key (.node bodyEntry bodyRows 0 [.interned ownerId])
        (.union unionEntry members level free) = .rightUnion ∧
      decision domain.key (.union unionEntry members level free)
        (.node bodyEntry bodyRows 0 [.interned ownerId]) = .swap := by
  have forwardOrder : compare (1 : Nat) 3 = .lt := by decide
  have reverseOrder : compare (3 : Nat) 1 = .gt := by decide
  constructor
  · simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, fresh, forwardOrder]
  · simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
      Value.referenceOf, Value.free, reverseOrder]

private theorem reference_union_branches
    (domain : Interned DomainKey) (ownerId : Nat)
    (unionEntry : Interned NodeKey) (members : List Node) (level : Nat) (free : List Reference)
    (fresh : pair unionEntry.identity ownerId ∉ domain.key.seen) :
    decision domain.key (.reference (.interned ownerId)) (.union unionEntry members level free) = .swap ∧
      decision domain.key (.union unionEntry members level free) (.reference (.interned ownerId)) = .leftUnion := by
  have forwardOrder : compare (4 : Nat) 3 = .gt := by decide
  have reverseOrder : compare (3 : Nat) 4 = .lt := by decide
  constructor
  · simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
      Value.referenceOf, Value.free, forwardOrder]
  · simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, fresh, reverseOrder]

private theorem union_code
    [DecidableEq Symbol]
    (domain : Interned DomainKey) (entry : Interned NodeKey) (members : List Node)
    (level : Nat) (free : List Reference) (alias : Node) (aliasFirst : Bool)
    (selected : decision domain.key (if aliasFirst then alias else .union entry members level free)
      (if aliasFirst then .union entry members level free else alias) =
        (if aliasFirst then .rightUnion else .leftUnion)) :
    compileNode ⟨domain, if aliasFirst then alias else .union entry members level free,
      if aliasFirst then .union entry members level free else alias⟩ =
      (SourceRecursiveIntersectionCode.walk (fun member : Node =>
        requestNode domain (if aliasFirst then alias else member) (if aliasFirst then member else alias)) members).bind
        (fun values => .work (makeUnion values) .pure) := by
  cases aliasFirst with
  | false =>
      change decision domain.key (.union entry members level free) alias = .leftUnion at selected
      change compileNode ⟨domain, .union entry members level free, alias⟩ =
        (SourceRecursiveIntersectionCode.walk (fun member : Node => requestNode domain member alias) members).bind
          (fun values => .work (makeUnion values) .pure)
      simp only [compileNode, selected]
  | true =>
      change decision domain.key alias (.union entry members level free) = .rightUnion at selected
      change compileNode ⟨domain, alias, .union entry members level free⟩ =
        (SourceRecursiveIntersectionCode.walk (fun member : Node => requestNode domain alias member) members).bind
          (fun values => .work (makeUnion values) .pure)
      simp only [compileNode, selected]

private theorem swap_code [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .swap) :
    compileNode request = requestNode request.domain request.right request.left := by
  simp only [compileNode, selected]

private theorem walk_profiles
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard) (sourceName : Nat)
    (pattern alias : Node) (request : NodeRequest Symbol Guard) (original : Checked width)
    (parentFuel bodySteps : Nat) (physicalOriginal : Physical original.native)
    (sourceGrowth : Grows sourceHeap original.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid original.operations)
    (plan : InputsThrough parentFuel (.code (.node request .pure)) original)
    (fields : FieldsThrough parentFuel (.code (.node request .pure)) original)
    (children : ∀ (closedOperand : Node) (child : NodeRequest Symbol Guard) (used childFuel childCount : Nat),
      0 < used → childFuel < parentFuel → used + childFuel ≤ parentFuel →
      childCount ≤ childFuel → used + childCount ≤ bodySteps + 1 →
      child.domain = request.domain → Profile sourceName closedOperand →
      height closedOperand ≤ height pattern →
      (alias = .reference (.interned sourceName) → height closedOperand < height pattern) →
      ((child.left = alias ∧ child.right = closedOperand) ∨
        (child.left = closedOperand ∧ child.right = alias)) →
      ∀ (next : Node → Code Symbol Guard Node) (first last : Checked width) (value : Node),
      Steps used (.code (.node request .pure)) original
        (.code ((requestNode child.domain child.left child.right).bind next)) first →
      Physical first.native → Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      InputsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      FieldsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      Available first.native.machine.heap child.left → Available first.native.machine.heap child.right →
      Steps childCount (.code (requestNode child.domain child.left child.right)) first
        (.code (.pure value)) last → Profile sourceName value)
    (child : Node → NodeRequest Symbol Guard) (members : List Node)
    (qualified : ∀ member ∈ members,
      (child member).domain = request.domain ∧ Profile sourceName member ∧ height member < height pattern ∧
      (((child member).left = alias ∧ (child member).right = member) ∨
        ((child member).left = member ∧ (child member).right = alias)))
    (jobs : List Node) (before : Checked width) (values : List Node) (after : Checked width) (count : Nat)
    (walked : SourceEqualityNativeDemandWalkExecution.Walk (fun member : Node =>
      requestNode (child member).domain (child member).left (child member).right) jobs before values after count)
    (used : Nat) (next : List Node → Code Symbol Guard Node)
    (origin : Steps used (.code (.node request .pure)) original
      (.code ((SourceRecursiveIntersectionCode.walk (fun member : Node =>
        requestNode (child member).domain (child member).left (child member).right) jobs).bind next)) before)
    (positive : 0 < used) (bounded : used + count ≤ parentFuel)
    (rawBound : used + count ≤ bodySteps + 1) (physical : Physical before.native)
    (included : ∀ member ∈ jobs, member ∈ members) :
    Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      (∀ value ∈ values, Available after.native.machine.heap value) ∧
      All₂ (fun _ value => Profile sourceName value) jobs values := by
  induction walked generalizing used next with
  | nil current =>
      exact ⟨physical, Extension.refl _, (by intro value member; cases member), .nil⟩
  | cons member rest before middle after value values firstCount restCount called tail ih =>
      let childNext : Node → Code Symbol Guard Node := fun value =>
        (SourceRecursiveIntersectionCode.walk (fun member : Node =>
          requestNode (child member).domain (child member).left (child member).right) rest).bind
          (fun values => next (value :: values))
      have atChild : Steps used (.code (.node request .pure)) original
          (.code ((requestNode (child member).domain (child member).left (child member).right).bind childNext)) before := by
        simpa only [SourceRecursiveIntersectionCode.walk, Code.bind_assoc, Code.bind, childNext] using origin
      have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        parentFuel used (.code (.node request .pure))
        (.code (requestNode (child member).domain (child member).left (child member).right)) childNext
        original before sourceHeap physicalOriginal plan fields operationsValid sourceGrowth atChild (by omega)
      obtain ⟨_checkedPrefix, childPhysical, _prefixExtension, childGrowth, childOperations,
        _operationGrowth, _boundPlan, childPlan, _boundFields, childFields⟩ := reached
      have ready := through_head (parentFuel - used)
        (.code (requestNode (child member).domain (child member).left (child member).right)) before childPlan
      obtain ⟨domain, ownProfile, strict, orientation⟩ := qualified member (included member List.mem_cons_self)
      have own := children member (child member) used (parentFuel - used) firstCount positive
        (by omega) (by omega) (by omega) (by omega) domain ownProfile (Nat.le_of_lt strict)
        (fun _ => strict) orientation childNext before middle value atChild
        childPhysical childGrowth childOperations childPlan childFields ready.1.2.1 ready.1.2.2 called
      have completed := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        (parentFuel - used) firstCount
        (.code (requestNode (child member).domain (child member).left (child member).right))
        (.code (.pure value)) .pure before middle sourceHeap childPhysical childPlan childFields
        childOperations childGrowth called (by omega)
      obtain ⟨checkedQuery, middlePhysical, queryExtension, _middleGrowth, _middleOperations,
        _queryOperationGrowth, _queryBoundPlan, _queryPlan, _queryBoundFields, _queryFields⟩ := completed
      have available := SourceCurrentNativeOpenRequestResults.node_result
        firstCount (child member) before middle value childPhysical checkedQuery
      have advanced := called.bind _ _ _ _ _ childNext
      have tailOrigin : Steps (used + firstCount) (.code (.node request .pure)) original
          (.code ((SourceRecursiveIntersectionCode.walk (fun member : Node =>
            requestNode (child member).domain (child member).left (child member).right) rest).bind
            (fun values => next (value :: values)))) middle :=
        atChild.trans _ _ _ _ _ _ _ _ advanced
      have restIncluded : ∀ candidate ∈ rest, candidate ∈ members := by
        intro candidate present
        exact included candidate (List.mem_cons_of_mem _ present)
      have later := ih (used + firstCount) (fun values => next (value :: values)) tailOrigin
        (by omega) (by omega) (by omega) middlePhysical restIncluded
      refine ⟨later.1, queryExtension.trans later.2.1, ?_, .cons own later.2.2.2⟩
      intro selected present
      cases present with
      | head => exact later.2.1.available value available
      | tail _ present => exact later.2.2.1 selected present

/-- Original mixed union bodies retain both authentic entry orders and all ordered member calls. -/
theorem current_stored_universe_mixed_union_body_profile_of_fuel_induction
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
    (_patternKind : tag pattern = 1 ∨ tag pattern = 3)
    (unionEntry : Interned NodeKey) (members : List Node) (level : Nat) (free : List Reference)
    (unionProfile : Profile entry.identity (.union unionEntry members level free))
    (unionBound : height (.union unionEntry members level free) ≤ height pattern)
    (useReference aliasFirst entryUniverseFirst : Bool)
    (referenceBound : useReference = true → height (.union unionEntry members level free) < height pattern)
    (initial : Control Output) (start entryBefore original before reader : Checked width)
    (startPhysical : Physical start.native) (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (wholeCount entryCount queryCount : Nat) (final : Control Output)
    (wholeActual : Trace wholeCount initial start final reader)
    (entryStrict : entryCount < wholeCount)
    (entryNext : Interned DomainKey → Code Symbol Guard Output)
    (entryPrefix : Steps entryCount initial start
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if entryUniverseFirst then .mu entry body depth ordinary else pattern)
        (if entryUniverseFirst then pattern else .mu entry body depth ordinary)
        (if entryUniverseFirst then entry.identity else patternId)
        (if entryUniverseFirst then patternId else entry.identity) entryNext)) entryBefore) :
    let universeValue : Node := .mu entry body depth ordinary
    let entryLeft : Node := if entryUniverseFirst then universeValue else pattern
    let entryRight : Node := if entryUniverseFirst then pattern else universeValue
    let firstId := if entryUniverseFirst then entry.identity else patternId
    let secondId := if entryUniverseFirst then patternId else entry.identity
    let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
      IntersectionEmptyDomain.emptyKey entryLeft entryRight firstId secondId
    let alias : Node := if useReference then .reference (.interned entry.identity) else body
    let operand : Node := .union unionEntry members level free
    let request : NodeRequest Symbol Guard := ⟨entered.1,
      if aliasFirst then alias else operand, if aliasFirst then operand else alias⟩
    ∀ (outerNext : Node → Code Symbol Guard Output),
    Steps queryCount initial start
      (.code ((requestNode request.domain request.left request.right).bind outerNext)) original →
    ∀ (parentFuel bodySteps : Nat) (result : Node) (after : Checked width)
      (finishNext : Node → Code Symbol Guard Node),
    SourceEqualityConstraintMemoAllocation.Valid original.operations →
    InputsThrough parentFuel (.code (.node request .pure)) original →
    FieldsThrough parentFuel (.code (.node request .pure)) original →
    Steps 1 (.code (.node request .pure)) original
      (.code ((compileNode request).bind finishNext)) before →
    bodySteps < parentFuel → queryCount + 1 + bodySteps ≤ wholeCount →
    Steps bodySteps (.code (compileNode request)) before (.code (.pure result)) after →
    (∀ (closedOperand : Node) (child : NodeRequest Symbol Guard) (used childFuel childCount : Nat),
      0 < used → childFuel < parentFuel → used + childFuel ≤ parentFuel →
      childCount ≤ childFuel → used + childCount ≤ bodySteps + 1 →
      child.domain = entered.1 → Profile entry.identity closedOperand →
      height closedOperand ≤ height pattern →
      (alias = .reference (.interned entry.identity) → height closedOperand < height pattern) →
      ((child.left = alias ∧ child.right = closedOperand) ∨
        (child.left = closedOperand ∧ child.right = alias)) →
      ∀ (next : Node → Code Symbol Guard Node) (first last : Checked width) (value : Node),
      Steps used (.code (.node request .pure)) original
        (.code ((requestNode child.domain child.left child.right).bind next)) first →
      Physical first.native → Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      InputsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      FieldsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      Available first.native.machine.heap child.left → Available first.native.machine.heap child.right →
      Steps childCount (.code (requestNode child.domain child.left child.right)) first
        (.code (.pure value)) last → Profile entry.identity value) →
    Profile entry.identity result ∧ Available after.native.machine.heap result ∧ Physical after.native ∧
    Extension original.native.machine after.native.machine ∧ Grows sourceHeap after.native.machine.heap ∧
    SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    SourceEqualityConstraintMemoAllocation.Grows original.operations after.operations ∧
    (∀ member ∈ members, Profile entry.identity member ∧ height member < height pattern) ∧
    decision entered.1.key alias operand = (if useReference then .swap else .rightUnion) ∧
    decision entered.1.key operand alias = (if useReference then .leftUnion else .swap) ∧
    ((compileNode request = requestNode entered.1 request.right request.left ∧
        Steps bodySteps (.code (requestNode entered.1 request.right request.left)) before
          (.code (.pure result)) after) ∨
      ∃ (values : List Node) (middle : Checked width) (walkCount : Nat),
        bodySteps = walkCount + 1 ∧
        SourceEqualityNativeDemandWalkExecution.Walk (fun member : Node =>
          requestNode entered.1 (if aliasFirst then alias else member) (if aliasFirst then member else alias))
          members before values middle walkCount ∧
        All₂ (fun _ value => Profile entry.identity value) members values ∧
        (∀ value ∈ values, Available middle.native.machine.heap value) ∧
        Steps walkCount (.code (compileNode request)) before
          (.code (.work (makeUnion values) .pure)) middle ∧
        Steps 1 (.code (.work (makeUnion values) .pure)) middle (.code (.pure result)) after ∧
        result = (run (makeUnion values) middle.native.machine.heap).1 ∧
        after = {middle with native := advance middle.native {middle.native.machine with heap :=
          (run (makeUnion values) middle.native.machine.heap).2}})
 := by
  let universeValue : Node := .mu entry body depth ordinary
  let entryLeft : Node := if entryUniverseFirst then universeValue else pattern
  let entryRight : Node := if entryUniverseFirst then pattern else universeValue
  let firstId := if entryUniverseFirst then entry.identity else patternId
  let secondId := if entryUniverseFirst then patternId else entry.identity
  let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey entryLeft entryRight firstId secondId
  let alias : Node := if useReference then .reference (.interned entry.identity) else body
  let operand : Node := .union unionEntry members level free
  let request : NodeRequest Symbol Guard := ⟨entered.1,
    if aliasFirst then alias else operand, if aliasFirst then operand else alias⟩
  dsimp only
  intro outerNext queryPrefix parentFuel bodySteps result after finishNext
    operationsValid plan fields dispatched smaller inside actual children
  change Steps 1 (Control.code (.node request .pure)) original
    (Control.code ((compileNode request).bind finishNext)) before at dispatched
  change Steps bodySteps (Control.code (compileNode request)) before
    (Control.code (.pure result)) after at actual
  have queryTotal : queryCount + (wholeCount - queryCount) = wholeCount := by omega
  have queryWhole : Trace (queryCount + (wholeCount - queryCount)) initial start final reader :=
    queryTotal.symm ▸ wholeActual
  have querySplit := SourceCurrentHereditaryNativePhysicalSplit.split queryPrefix queryWhole
  have originalFacts := SourceCurrentNativeEnterCommonOperand.checked_trace_extension querySplit.1 startPhysical
  have originalGrowth : Grows sourceHeap original.native.machine.heap :=
    grows_trans sourceGrowth originalFacts.2.heap
  have current := through_head parentFuel (.code (.node request .pure)) original plan
  have operandOriginal : Available original.native.machine.heap operand := by
    cases aliasFirst with
    | false => exact current.1.2.1
    | true => exact current.1.2.2
  have memberAdmission : ∀ member ∈ members, Profile entry.identity member ∧ height member < height pattern := by
    intro member present
    have admitted := SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms
      original.native.machine.heap originalFacts.1.machine.1 entry.identity unionEntry members level free
      operandOriginal unionProfile.1 unionProfile.2 member present
    exact ⟨⟨admitted.2.1, admitted.2.2⟩, Nat.lt_of_lt_of_le
      (SourceSynthesisUniversePrefixHeight.member_lt unionEntry members level free member present) unionBound⟩
  have firstResources := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel 1 (.code (.node request .pure)) (.code (compileNode request)) finishNext
    original before sourceHeap originalFacts.1 plan fields operationsValid originalGrowth dispatched (by omega)
  obtain ⟨_firstChecked, beforePhysical, _firstExtension, beforeGrowth, beforeOperations,
    _firstOperationsGrowth, _boundBeforePlan, beforePlan, _boundBeforeFields, beforeFields⟩ := firstResources
  have operandBefore : Available before.native.machine.heap operand :=
    _firstExtension.available operand operandOriginal
  have liftedDispatch := dispatched.bind _ _ _ _ _ outerNext
  have joinedProducer := queryPrefix.trans _ _ _ _ _ _ _ _ liftedDispatch
  have producerPrefix : Steps (queryCount + 1) initial start
      (.code ((compileNode request).bind (fun value => (finishNext value).bind outerNext))) before := by
    simpa only [Control.bind, Code.bind_assoc] using joinedProducer
  have producerTotal : (queryCount + 1) + (wholeCount - (queryCount + 1)) = wholeCount := by omega
  have producerWhole : Trace ((queryCount + 1) + (wholeCount - (queryCount + 1)))
      initial start final reader := producerTotal.symm ▸ wholeActual
  have producerSplit := SourceCurrentHereditaryNativePhysicalSplit.split producerPrefix producerWhole
  have atReader := SourceCurrentNativeEnterCommonOperand.checked_trace_extension producerSplit.2 beforePhysical
  have operandReader : Available reader.native.machine.heap operand := atReader.2.available operand operandBefore
  have entryTotal : entryCount + (wholeCount - entryCount) = wholeCount := by omega
  have entryWhole : Trace (entryCount + (wholeCount - entryCount)) initial start final reader :=
    entryTotal.symm ▸ wholeActual
  have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split entryPrefix entryWhole
  have entryFacts := SourceCurrentNativeEnterCommonOperand.checked_trace_extension entrySplit.1 startPhysical
  have entryLength : wholeCount - entryCount = (wholeCount - entryCount - 1) + 1 := by omega
  have entryActual : Trace ((wholeCount - entryCount - 1) + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext))
      entryBefore final reader := entryLength ▸ entrySplit.2
  obtain ⟨_entryOne, _entryTail, _entryHeap, _entryDomains, _entryOperations, _oldDomain,
      _leftAtEntry, _rightAtEntry, leftReader, rightReader, _domainAfterEntry, _domainAtReader,
      enteredKey, _entryExtension, _sameRecord⟩ :=
    SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
      IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext
      (wholeCount - entryCount - 1) entryBefore reader final entryFacts.1 entryActual
  change entered.1.key = extend IntersectionEmptyDomain.emptyKey
    ((SourceRecursiveIntersectionEnvironment.bindings entryLeft entryRight).map Prod.fst)
    (pair firstId secondId) at enteredKey
  have patternReader : Available reader.native.machine.heap pattern := by
    cases entryUniverseFirst with
    | false => exact leftReader
    | true => exact rightReader
  have originalPair : pair firstId secondId = pair entry.identity patternId := by
    cases entryUniverseFirst with
    | false =>
        change pair patternId entry.identity = pair entry.identity patternId
        simp only [pair, Nat.min_comm, Nat.max_comm]
    | true => rfl
  have seenOnly : ∀ candidate, candidate ∈ entered.1.key.seen → candidate = pair entry.identity patternId := by
    intro candidate seen
    rw [enteredKey] at seen
    rcases (extend_seen IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.bindings entryLeft entryRight).map Prod.fst)
      (pair firstId secondId) candidate).mp seen with same | old
    · exact same.trans originalPair
    · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at old
  obtain ⟨bodyEntry, _marker, arrow, rows, bodyShape, bodyAvailable, _sourceRows⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      before.native.machine.heap beforePhysical.machine.1 beforeGrowth
  let bodyRows := canonicalEdges (arrow :: rows)
  have actualBody : Available before.native.machine.heap (.node bodyEntry bodyRows 0 [.interned entry.identity]) :=
    bodyShape ▸ bodyAvailable
  have ownerAvailable : Available before.native.machine.heap universeValue :=
    beforePhysical.machine.1.cached.nodes key _ (beforeGrowth.nodeRecords key _ stored)
  have bodyApart : bodyEntry.identity ≠ entry.identity :=
    physical_identity_apart_owner before.native.machine.heap beforePhysical.machine.1 entry body depth ordinary
      ownerAvailable (.node bodyEntry bodyRows 0 [.interned entry.identity]) actualBody bodyEntry.identity rfl
      (by intro impossible; cases impossible)
  have unionApart : unionEntry.identity ≠ entry.identity :=
    physical_identity_apart_owner before.native.machine.heap beforePhysical.machine.1 entry body depth ordinary
      ownerAvailable operand operandBefore unionEntry.identity rfl (by
        intro impossible
        change (Value.union unionEntry members level free : Node) = Value.mu entry body depth ordinary at impossible
        cases impossible)
  have bodyNotReference : body ≠ .reference (.interned entry.identity) := by
    intro impossible
    rw [bodyShape] at impossible
    cases impossible
  have aliasStrict : alias = .reference (.interned entry.identity) → height operand < height pattern := by
    intro same
    cases useReference with
    | false => exact False.elim (bodyNotReference same)
    | true => exact referenceBound rfl
  have controls :
      decision entered.1.key alias operand = (if useReference then .swap else .rightUnion) ∧
      decision entered.1.key operand alias = (if useReference then .leftUnion else .swap) := by
    cases useReference with
    | false =>
        have apart := pair_apart_owner bodyEntry.identity unionEntry.identity entry.identity patternId bodyApart unionApart
        have fresh : pair bodyEntry.identity unionEntry.identity ∉ entered.1.key.seen := by
          intro seen
          exact apart (seenOnly _ seen)
        have physicalControl := body_union_branches entered.1 entry.identity bodyEntry bodyRows
          unionEntry members level free fresh
        have forwardTransport := congrArg (fun candidate : Node => decision entered.1.key candidate operand) bodyShape
        have reverseTransport := congrArg (fun candidate : Node => decision entered.1.key operand candidate) bodyShape
        exact ⟨forwardTransport.trans physicalControl.1, reverseTransport.trans physicalControl.2⟩
    | true =>
        have strict := referenceBound rfl
        have different := SourceSynthesisUniverseMixedDescendantFreshness.strict_prefix_height_identity_ne
          reader.native.machine.heap atReader.1.machine.1 pattern operand patternReader operandReader
          patternClosed unionProfile.1 patternId unionEntry.identity patternIdentity rfl strict
        have fresh : pair unionEntry.identity entry.identity ∉ entered.1.key.seen := by
          intro seen
          have same := seenOnly _ seen
          have lower := congrArg Prod.fst same
          have upper := congrArg Prod.snd same
          simp only [pair] at lower upper
          apply different
          omega
        exact reference_union_branches entered.1 entry.identity unionEntry members level free fresh
  have bodyBound := actual.bind _ _ _ _ _ finishNext
  have finalPrefix := dispatched.trans _ _ _ _ _ _ _ _ bodyBound
  have atFinal : Steps (1 + bodySteps) (.code (.node request .pure)) original
      ((Control.code (.pure result)).bind finishNext) after := by
    simpa only [Control.bind] using finalPrefix
  have finalResources := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel (1 + bodySteps) (.code (.node request .pure)) (.code (.pure result)) finishNext
    original after sourceHeap originalFacts.1 plan fields operationsValid originalGrowth atFinal (by omega)
  obtain ⟨checkedWhole, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
    _boundAfterPlan, _afterPlan, _boundAfterFields, _afterFields⟩ := finalResources
  have bodySplit := SourceCurrentHereditaryNativePhysicalSplit.split dispatched checkedWhole
  have bodyTrace := SourceCurrentHereditaryNativePhysicalSplit.unbind actual finishNext bodySplit.2
  let child : Node → NodeRequest Symbol Guard := fun member => ⟨entered.1,
    if aliasFirst then alias else member, if aliasFirst then member else alias⟩
  let build : List Node → Code Symbol Guard Node := fun values => .work (makeUnion values) .pure
  have compiledCases :
      compileNode request = requestNode entered.1 request.right request.left ∨
      compileNode request = (SourceRecursiveIntersectionCode.walk (fun member : Node =>
        requestNode (child member).domain (child member).left (child member).right) members).bind build := by
    cases useReference with
    | false =>
        cases aliasFirst with
        | false =>
            have selected : decision request.domain.key request.left request.right = .swap := controls.2
            exact .inl (swap_code request selected)
        | true =>
            have selected : decision request.domain.key request.left request.right = .rightUnion := controls.1
            exact .inr (union_code entered.1 unionEntry members level free alias true selected)
    | true =>
        cases aliasFirst with
        | false =>
            have selected : decision request.domain.key request.left request.right = .leftUnion := controls.2
            exact .inr (union_code entered.1 unionEntry members level free alias false selected)
        | true =>
            have selected : decision request.domain.key request.left request.right = .swap := controls.1
            exact .inl (swap_code request selected)
  rcases compiledCases with swapped | compiled
  · let reversed : NodeRequest Symbol Guard := ⟨entered.1, request.right, request.left⟩
    have childOrigin : Steps 1 (.code (.node request .pure)) original
        (.code ((requestNode reversed.domain reversed.left reversed.right).bind finishNext)) before := by
      simpa only [swapped] using dispatched
    have childTrace : Steps bodySteps (.code (requestNode reversed.domain reversed.left reversed.right)) before
        (.code (.pure result)) after := by simpa only [swapped] using actual
    have childChecked : Trace bodySteps (.code (requestNode reversed.domain reversed.left reversed.right)) before
        (.code (.pure result)) after := by simpa only [swapped] using bodyTrace
    have childPlan : InputsThrough (parentFuel - 1)
        (.code (requestNode reversed.domain reversed.left reversed.right)) before := by
      simpa only [swapped] using beforePlan
    have childFields : FieldsThrough (parentFuel - 1)
        (.code (requestNode reversed.domain reversed.left reversed.right)) before := by
      simpa only [swapped] using beforeFields
    have ready := through_head (parentFuel - 1)
      (.code (requestNode reversed.domain reversed.left reversed.right)) before childPlan
    have orientation : (reversed.left = alias ∧ reversed.right = operand) ∨
        (reversed.left = operand ∧ reversed.right = alias) := by
      cases aliasFirst with
      | false => exact .inl ⟨rfl, rfl⟩
      | true => exact .inr ⟨rfl, rfl⟩
    have profile := children operand reversed 1 (parentFuel - 1) bodySteps
      (by decide) (by omega) (by omega) (by omega) (by omega) rfl unionProfile unionBound aliasStrict orientation
      finishNext before after result childOrigin beforePhysical beforeGrowth beforeOperations
      childPlan childFields ready.1.2.1 ready.1.2.2 childTrace
    have available := SourceCurrentNativeOpenRequestResults.node_result
      bodySteps reversed before after result beforePhysical childChecked
    exact ⟨profile, available, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
      memberAdmission, controls.1, controls.2, .inl ⟨swapped, childTrace⟩⟩
  · have acceptedTrace : Trace bodySteps
        ((Control.code (SourceRecursiveIntersectionCode.walk (fun member : Node =>
          requestNode (child member).domain (child member).left (child member).right) members)).bind build)
        before (.code (.pure result)) after := by
      simpa only [compiled, Control.bind] using bodyTrace
    obtain ⟨walkCount, workCount, values, middle, total, walkTrace, workTrace⟩ :=
      SourceCurrentHereditaryNativePhysicalSplit.bind_split
        (.code (SourceRecursiveIntersectionCode.walk (fun member : Node =>
          requestNode (child member).domain (child member).left (child member).right) members))
        build before after result acceptedTrace
    have walked := SourceEqualityNativeDemandWalkExecution.trace_walk (fun member : Node =>
      requestNode (child member).domain (child member).left (child member).right)
      members walkCount before middle values walkTrace.steps
    obtain ⟨workIsOne, sameResult, sameAfter, _workInputs⟩ :=
      SourceCurrentAllocatedNativeSemanticTraceReadback.work_readback
        (makeUnion values) workCount middle after result workTrace
    have qualified : ∀ member ∈ members,
        (child member).domain = request.domain ∧ Profile entry.identity member ∧ height member < height pattern ∧
        (((child member).left = alias ∧ (child member).right = member) ∨
          ((child member).left = member ∧ (child member).right = alias)) := by
      intro member present
      refine ⟨rfl, (memberAdmission member present).1, (memberAdmission member present).2, ?_⟩
      cases aliasFirst with
      | false => exact .inr ⟨rfl, rfl⟩
      | true => exact .inl ⟨rfl, rfl⟩
    let fullNext : List Node → Code Symbol Guard Node := fun values => (build values).bind finishNext
    have walkOrigin : Steps 1 (.code (.node request .pure)) original
        (.code ((SourceRecursiveIntersectionCode.walk (fun member : Node =>
          requestNode (child member).domain (child member).left (child member).right) members).bind fullNext)) before := by
      simpa only [compiled, Code.bind_assoc, fullNext] using dispatched
    have observed := walk_profiles sourceHeap entry.identity pattern alias request original parentFuel bodySteps
      originalFacts.1 originalGrowth operationsValid plan fields children child members qualified
      members before values middle walkCount walked 1 fullNext walkOrigin (by decide) (by omega) (by omega)
      beforePhysical (by intro member present; exact present)
    have allProfiles := profiles_of_all_two entry.identity observed.2.2.2
    have builtProfile : Profile entry.identity (run (makeUnion values) middle.native.machine.heap).1 := by
      refine ⟨MergedColdReaderClosedInputs.makeUnion_closed values middle.native.machine.heap
        observed.1.machine.1 observed.2.2.1 (fun value present => (allProfiles value present).1), ?_⟩
      intro atom occurrence
      obtain ⟨value, present, included⟩ := InternedBoundaryAtoms.makeUnion_atom_origin values
        middle.native.machine.heap observed.1.machine.1.coherent observed.1.machine.1.cached
        observed.1.machine.1.linked observed.2.2.1 atom occurrence
      exact (allProfiles value present).2 atom included
    have verified := InternedNestedFacts.union_verified values middle.native.machine.heap
      observed.1.machine.1 observed.2.2.1
    have available : Available after.native.machine.heap result := by
      rw [sameResult, sameAfter]
      exact verified.result _ _ rfl
    have profile : Profile entry.identity result := by
      rw [sameResult]
      exact builtProfile
    have throughWork : Steps walkCount (.code (compileNode request)) before
        (.code (.work (makeUnion values) .pure)) middle := by
      have appended := walked.trace.bind _ _ _ _ _ build
      simpa only [compiled, Control.bind, build, Code.bind] using appended
    have workStep : Steps 1 (.code (.work (makeUnion values) .pure)) middle (.code (.pure result)) after := by
      simpa only [workIsOne] using workTrace.steps
    exact ⟨profile, available, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
      memberAdmission, controls.1, controls.2,
      .inr ⟨values, middle, walkCount, by omega, walked, observed.2.2.2, observed.2.2.1,
        throughWork, workStep, sameResult, sameAfter⟩⟩

end MicroCFTA.SourceCurrentAllocatedNativeMixedUnionProfile
