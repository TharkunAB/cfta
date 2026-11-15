import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistoryDefinitions
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryDispatchOrigin
import MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult
import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalOuterReclosure
import MicroCFTA.SourceCurrentAllocatedNativePrefixOperations

/-!
# Source diagonal completion from the past cache law

The actual entry and producer belong to the same root trace.
The entry preserves the full pattern at the common reader.
The past cache law supplies the returned B/R product shape.
The actual optional binder recloses the original stored universe.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAuthenticDiagonalOuterFinish
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativeGeneralCMHistory (AuthenticEntry)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid

set_option autoImplicit false

private theorem mu_code [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .leftMu) :
    compileNode request = compileMu request.domain request.left request.right := by
  simp only [compileNode, selected]

private theorem optional_reclosed_trace
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (binder : Nat × Nat) (product expected : Value Symbol Guard)
    (before after : Checked width) (count : Nat) (result : Value Symbol Guard)
    (one : SourceEqualityNativeDemand.step (.code (.optionalBinder binder product .pure)) before =
      .yielded (.code (.pure expected)) before)
    (actual : Steps count (.code (.optionalBinder binder product .pure)) before (.code (.pure result)) after) :
    count = 1 ∧ result = expected ∧ after = before := by
  cases count with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      have same := Outcome.yielded.inj (chosen.symm.trans one)
      rw [same.1, same.2] at tail
      have terminal := pure_trace remaining expected result before after tail
      have remainingZero : remaining = 0 := terminal.1
      exact ⟨by omega, terminal.2.1.symm, terminal.2.2.symm⟩

/-- The actual diagonal parent uses its returned B/R child at the same finish. -/
theorem diagonal_outer_finish_of_past_coherent_laws
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (fuel wholeCount finishCount : Nat)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (domain actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntry (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary pattern patternId domain)
    (sameKey : actualDomain.key = domain.key)
    (parentHandle : Nat) (value : Value Symbol Guard)
    (rest : Code Symbol Guard (Value Symbol Guard)) (beforeFinish : Checked width)
    (readerControl : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width) readerControl reader)
    (finishWithin : finishCount + 1 ≤ wholeCount)
    (actual : Trace finishCount (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishNode parentHandle value rest)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells parentHandle =
      some ⟨⟨actualDomain, .mu entry body depth ordinary,
        .reference (.interned entry.identity)⟩, .evaluating⟩)
    (plan : InputsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (past :
      Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity
        (extend (extend domain.key [entry.identity] (pair entry.identity entry.identity))
          [entry.identity] (pair bodyId entry.identity))
        (extend domain.key [entry.identity] (pair entry.identity entry.identity))
        body (.mu entry body depth ordinary)) beforeFinish.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult beforeFinish.native.edges) :
    value = .mu entry body depth ordinary := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let initialState : Checked width := ⟨initial width machine, operations⟩
  let rootControl : Control (Value Symbol Guard) := .code (.node rootRequest .pure)
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let request : NodeRequest Symbol Guard := ⟨actualDomain, universeValue, referenceValue⟩
  have initialPhysical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid
  have atReader := SourceCurrentNativeEnterCommonOperand.checked_trace_extension wholeActual initialPhysical
  have readerGrowth : Grows sourceHeap reader.native.machine.heap :=
    InternedConstructorTemplates.grows_trans sourceGrowth atReader.2.heap
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed, entryBefore,
    entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, _orderedTuple, _entryOne, domainEq⟩ := entryData
  let entryLeft := if universeFirst then universeValue else pattern
  let entryRight := if universeFirst then pattern else universeValue
  let firstId := if universeFirst then entry.identity else patternId
  let secondId := if universeFirst then patternId else entry.identity
  let sourceDomain := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  change domain = sourceDomain.1 at domainEq
  have entryTotal : entryUsed + (wholeCount - entryUsed) = wholeCount := by omega
  have entryWhole : Trace (entryUsed + (wholeCount - entryUsed)) rootControl initialState readerControl reader :=
    entryTotal.symm ▸ wholeActual
  have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split entryPrefix.steps entryWhole
  have entryPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension entrySplit.1 initialPhysical
  have entryLength : wholeCount - entryUsed = (wholeCount - entryUsed - 1) + 1 := by omega
  have entryActual : Trace ((wholeCount - entryUsed - 1) + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext))
      entryBefore readerControl reader := entryLength ▸ entrySplit.2
  obtain ⟨_entryStep, _entryTail, _entryHeap, _entryDomains, _entryOperations, _oldDomain,
    _leftAtEntry, _rightAtEntry, leftReader, rightReader, _domainAfterEntry, _domainAtReader,
    _enteredKey, _entryExtension, _sameRecord⟩ :=
    SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
      IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext
      (wholeCount - entryUsed - 1) entryBefore reader readerControl entryPhysical.1 entryActual
  have patternReader : Available reader.native.machine.heap pattern := by
    cases universeFirst with
    | false => exact leftReader
    | true => exact rightReader
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      reader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
  have bodyIdEq : bodyEntry.identity = bodyId := by
    have observed : identity body = some bodyEntry.identity := by
      simp only [bodyShape, identity]
    exact Option.some.inj (observed.symm.trans bodyIdentity)
  subst bodyId
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
    body universeValue bodyEntry.identity entry.identity
  dsimp only at sourceFacts
  have bodySelected : decision bodyFirst.1.key universeValue referenceValue = .leftMu := sourceFacts.1
  have sourceValid : Cache.Valid sourceDomain.2 :=
    (IntersectionEmptyDomain.make_correct entryBefore.native.machine.domains entryPhysical.1.machine.2 _).1
  have bodyKey := SourceRecursiveIntersectionSchedule.entered_key sourceDomain.2 sourceValid sourceDomain.1.key
    body universeValue bodyEntry.identity entry.identity
  have tagOrder : compare (2 : Nat) 4 = .lt := by decide
  have diagonalFresh : pair entry.identity entry.identity ∉ bodyFirst.1.key.seen := by
    intro member
    have repeated : decision bodyFirst.1.key universeValue referenceValue =
        .repeated (pair entry.identity entry.identity) := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity,
        universeValue, referenceValue, Value.referenceOf, Value.free, member, tagOrder]
    rw [repeated] at bodySelected
    cases bodySelected
  have sourceFresh : pair entry.identity entry.identity ∉ sourceDomain.1.key.seen := by
    intro member
    apply diagonalFresh
    change pair entry.identity entry.identity ∈ bodyFirst.1.key.seen
    rw [bodyKey]
    exact (extend_seen _ _ _ _).mpr (Or.inr member)
  have sourceSameKey : actualDomain.key = sourceDomain.1.key :=
    sameKey.trans (congrArg (fun current => current.key) domainEq)
  have actualFresh : pair entry.identity entry.identity ∉ actualDomain.key.seen := by
    rw [sourceSameKey]
    exact sourceFresh
  have selected : decision request.domain.key request.left request.right = .leftMu := by
    simp [request, decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      universeValue, referenceValue, Value.referenceOf, Value.free, actualFresh, tagOrder]
  have compiled := mu_code request selected
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, resume, total, _queryBeforeFinish, _queryBound,
    queryPrefix, dispatched, _isolated, queryPhysical, _queryReady, _querySafe, _bodyOwner, bodyActual, _resumeEq⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_initial_query_finish
      rootRequest machine machineValid operations fuel finishCount parentHandle request value rest
      beforeFinish (by omega) actual owner
  have beforePhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension dispatched queryPhysical).1
  let allocated := SourceRecursiveIntersectionEnvironment.enter beforeBody.native.machine.domains request.domain.key
    request.left request.right entry.identity entry.identity
  let started : Checked width :=
    {beforeBody with native := advance beforeBody.native {beforeBody.native.machine with domains := allocated.2}}
  let binder := pair entry.identity entry.identity
  let childCode := requestNode allocated.1 body referenceValue
  let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun product => .optionalBinder binder product .pure
  let finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun result => .finishNode parentHandle result (resume result)
  let lifted : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun product => (next product).bind finishNext
  have leftRead : identity request.left = some entry.identity := rfl
  have one : step (.code (compileNode request)) beforeBody =
      .yielded (.code (childCode.bind next)) started := by
    rw [compiled]
    have receipt := SourceCurrentAllocatedNativeMuSource.enter_prefix request beforeBody
      entry.identity entry.identity leftRead rfl
    simpa only [childCode, requestNode, Code.bind, next, binder, started, allocated,
      request, universeValue, referenceValue, SourceRecursiveIntersectionKernel.body] using receipt
  have bodyEnter : Steps 1 (.code (compileNode request)) beforeBody
      (.code (childCode.bind next)) started := .cons _ _ _ _ _ _ 0 one (.refl _ _)
  have names : (SourceRecursiveIntersectionEnvironment.bindings request.left request.right).map Prod.fst =
      [entry.identity] := by
    simp only [request, universeValue, referenceValue, SourceRecursiveIntersectionEnvironment.bindings,
      SourceRecursiveIntersectionEnvironment.binder, List.append_nil, List.map_cons, List.map_nil]
  have keyCalculation := SourceRecursiveIntersectionSchedule.entered_key beforeBody.native.machine.domains
    beforePhysical.machine.2 request.domain.key request.left request.right entry.identity entry.identity
  change allocated.1.key = extend request.domain.key
    ((SourceRecursiveIntersectionEnvironment.bindings request.left request.right).map Prod.fst)
    (pair entry.identity entry.identity) at keyCalculation
  have allocatedKey : allocated.1.key =
      extend domain.key [entry.identity] (pair entry.identity entry.identity) := by
    have normalized : allocated.1.key = extend actualDomain.key [entry.identity]
        (pair entry.identity entry.identity) :=
      keyCalculation.trans (congrArg
        (fun bindings => extend request.domain.key bindings (pair entry.identity entry.identity)) names)
    exact normalized.trans (congrArg
      (fun current => extend current [entry.identity] (pair entry.identity entry.identity)) sameKey)
  have liftedBody := bodyEnter.bind _ _ _ _ _ finishNext
  have rootBody := queryPrefix.steps.trans _ _ _ _ _ _ _ _ dispatched.steps
  have intoChild := rootBody.trans _ _ _ _ _ _ _ _ liftedBody
  have childOrigin : Steps (queryUsed + 2) rootControl initialState
      (.code (childCode.bind lifted)) started := by
    simpa only [Control.bind, Code.bind_assoc, Code.bind, finishNext, lifted, Nat.add_assoc] using intoChild
  cases bodyCount with
  | zero =>
      have impossible := steps_zero _ _ _ _ bodyActual
      rw [impossible.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ bodyActual
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (chosen.symm.trans one)
      obtain ⟨childCount, optionalCount, product, middle, splitCount, childActual, optionalActual⟩ :=
        steps_bind_inverse remaining (.code childCode) next started beforeFinish value tail
      have keyed : ∃ key, SourceRecursiveIntersectionMemo.requestKey width allocated.1 body referenceValue = some key := by
        rw [bodyShape]
        exact ⟨_, rfl⟩
      obtain ⟨childKey, childKeyEq⟩ := keyed
      have childPast := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_node_finish
        (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
          entry.identity entry.identity entry.identity
          (extend (extend domain.key [entry.identity] (pair entry.identity entry.identity))
            [entry.identity] (pair bodyEntry.identity entry.identity))
          (extend domain.key [entry.identity] (pair entry.identity entry.identity)) body universeValue)
        SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult
        rootRequest machine machineValid operations fuel finishCount (queryUsed + 2) childCount
        parentHandle value rest beforeFinish (by omega) actual past
        ⟨allocated.1, body, referenceValue⟩ childKey childKeyEq lifted started middle product
        (by omega) childOrigin childActual
      have shape : SourceCurrentAllocatedNativeCoherentOpenBodyResult.ProductShape
          entry.identity entry.identity entry.identity body product :=
        childPast.1.2 allocatedKey rfl rfl
      have childResources := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        fuel (queryUsed + 2) rootControl (.code childCode) lifted initialState started
        sourceHeap initialPhysical plan fields operationsValid sourceGrowth childOrigin (by omega)
      obtain ⟨_checkedOrigin, childPhysical, _childExtension, childGrowth, _childOperations,
        _childOperationsGrowth, _boundChildPlan, childPlan, _boundChildFields, _childFields⟩ := childResources
      have atEnd := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
        (fuel - (queryUsed + 2)) childCount (.code childCode) (.code (.pure product)) .pure
        started middle childPhysical childPlan childActual (by omega)
      have middleGrowth : Grows sourceHeap middle.native.machine.heap :=
        InternedConstructorTemplates.grows_trans childGrowth atEnd.2.2.1.heap
      have available : Available middle.native.machine.heap product :=
        SourceCurrentNativeOpenRequestResults.node_result childCount
          ⟨allocated.1, body, referenceValue⟩ started middle product childPhysical atEnd.1
      obtain ⟨_reclosed, optionalOne, _optionalDone⟩ :=
        SourceCurrentAllocatedNativeCoherentOpenBodyResult.stored_open_product_optional_reclosure
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          middle atEnd.2.1.machine.1 middleGrowth entry.identity entry.identity product available shape
      exact (optional_reclosed_trace binder product universeValue middle beforeFinish optionalCount value
        optionalOne optionalActual).2.1

end MicroCFTA.SourceCurrentAllocatedNativeAuthenticDiagonalOuterFinish
