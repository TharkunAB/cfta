import MicroCFTA.SourceCurrentAllocatedNativePastEntryInnerPayloadTransport
import MicroCFTA.SourceCurrentAllocatedNativePrefixOperations
import MicroCFTA.SourceEqualityNativeDemandContinuation

namespace MicroCFTA.SourceCurrentAllocatedNativePastEntryNextQueryInnerLaws
open Cache InternedConstructorTemplates
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity pair)
open SourceRecursiveIntersectionDomain (extend names extend_seen)
open SourceEqualityNativeDemand
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeGeneralCMHistory (AuthenticEntry)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

open Language InternedProbeProvenance
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionControl
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (KnownResult)
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid

private theorem reference_code [DecidableEq Symbol]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (chosen : decision domain.key (.reference (.interned name) : Value Symbol Guard)
      (.reference (.interned name)) = .leftReference) :
    compileNode (⟨domain, .reference (.interned name), .reference (.interned name)⟩ : NodeRequest Symbol Guard) =
      compileReference domain name (.reference (.interned name)) true := by
  simp only [compileNode, chosen]

private theorem reference_read_step
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other value : Value Symbol Guard) (current : SourceEqualityNativeDemand.State width)
    (bound : name ∈ names domain.key)
    (read : SourcePreparedSharedRows.read current.native.machine.heap name = some value) :
    SourceEqualityNativeDemand.step (.code (compileReference domain name other true)) current =
      .yielded (.code (requestNode domain value other)) current := by
  simp [compileReference, bound, SourceEqualityNativeDemand.step,
    SourceRecursiveIntersectionNative.step, read, SourceEqualityNativeDemand.lift]

private theorem body_first_next_query
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel wholeCount : Nat) (readerControl : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) readerControl reader)
    (fullPattern : Value Symbol Guard) (patternId : Nat)
    (oldDomain newDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntry (width := width) oldRoot machine operations wholeCount
      entry body depth ordinary fullPattern patternId oldDomain)
    (sameKey : newDomain.key = oldDomain.key)
    (inputs : InputsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (newRequest : NodeRequest Symbol Guard) (newFuel : Nat)
    (newInputs : InputsThrough newFuel (.code (.node newRequest .pure)) reader)
    (newFields : FieldsThrough newFuel (.code (.node newRequest .pure)) reader) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let selectedKey := extend newDomain.key [entry.identity] (pair bodyId entry.identity)
    (Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId selectedKey body universeValue)
        (execute newFuel (.code (.node newRequest .pure)) reader).state.native.nodes ∧
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
        entry.identity bodyId selectedKey universeValue)
        (execute newFuel (.code (.node newRequest .pure)) reader).state.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (final : Checked width), count ≤ newFuel →
      Steps count (.code (.node newRequest .pure)) reader (.code (.pure value)) final →
      SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId selectedKey body universeValue newRequest value) := by
  have inherited :=
    SourceCurrentAllocatedNativePastEntryInnerPayloadTransport.inner_payloads_of_past_authentic_entry_at_equal_key
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity oldRoot machine machineValid sourceGrowth operations operationsValid
      fuel wholeCount readerControl reader wholeBound wholeActual fullPattern patternId
      oldDomain newDomain authentic sameKey inputs fields
      wholeCount readerControl reader (Nat.le_refl _) wholeActual
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let initialState : Checked width := ⟨initial width machine, operations⟩
  let rootControl : Control (Value Symbol Guard) := .code (.node oldRoot .pure)
  have initialPhysical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid
  have atReader := SourceCurrentNativeEnterCommonOperand.checked_trace_extension wholeActual initialPhysical
  have readerGrowth : Grows sourceHeap reader.native.machine.heap :=
    InternedConstructorTemplates.grows_trans sourceGrowth atReader.2.heap
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed, entryBefore,
    entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, _orderedTuple, _entryOne, domainEq⟩ := entryData
  let entryLeft := if universeFirst then universeValue else fullPattern
  let entryRight := if universeFirst then fullPattern else universeValue
  let firstId := if universeFirst then entry.identity else patternId
  let secondId := if universeFirst then patternId else entry.identity
  let sourceDomain := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue fullPattern entry.identity patternId
  change oldDomain = sourceDomain.1 at domainEq
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
  have patternReader : Available reader.native.machine.heap fullPattern := by
    cases universeFirst with
    | false => exact leftReader
    | true => exact rightReader
  obtain ⟨bodyEntry, bodyRows, bodyShape, bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      reader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      fullPattern patternReader patternClosed patternId patternIdentity patternKind
  obtain ⟨readEntry, readRows, readShape, readFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstReferenceRead.current_stored_universe_body_first_reference_read
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      reader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      fullPattern patternReader patternClosed patternId patternIdentity patternKind
  have sameEntry : readEntry = bodyEntry := (Value.node.inj (readShape.symm.trans bodyShape)).1
  have sameRows : readRows = bodyRows := (Value.node.inj (readShape.symm.trans bodyShape)).2.1
  subst readEntry
  subst readRows
  have bodyIdEq : bodyEntry.identity = bodyId := by
    have observed : identity body = some bodyEntry.identity := by
      simp only [bodyShape, identity]
    exact Option.some.inj (observed.symm.trans bodyIdentity)
  subst bodyId
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
    body universeValue bodyEntry.identity entry.identity
  dsimp only at sourceFacts readFacts
  have sourceDomainValid : Cache.Valid sourceDomain.2 :=
    (IntersectionEmptyDomain.make_correct entryBefore.native.machine.domains entryPhysical.1.machine.2 _).1
  have sourceDomainKey : sourceDomain.1.key = extend IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.bindings universeValue fullPattern).map Prod.fst)
      (pair entry.identity patternId) :=
    SourceRecursiveIntersectionSchedule.entered_key entryBefore.native.machine.domains entryPhysical.1.machine.2 IntersectionEmptyDomain.emptyKey
      universeValue fullPattern entry.identity patternId
  have bodyKey : bodyFirst.1.key = extend sourceDomain.1.key
      ((SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst)
      (pair bodyEntry.identity entry.identity) :=
    SourceRecursiveIntersectionSchedule.entered_key sourceDomain.2 sourceDomainValid sourceDomain.1.key
      body universeValue bodyEntry.identity entry.identity
  have diagonalParts (first second owner : Nat) (same : pair first second = pair owner owner) :
      first = owner ∧ second = owner := by
    have lower := congrArg Prod.fst same
    have upper := congrArg Prod.snd same
    simp only [pair, Nat.min_self, Nat.max_self] at lower upper
    omega
  have freshBodyPair : pair bodyEntry.identity bodyEntry.identity ∉ bodyFirst.1.key.seen := by
    intro member
    rw [bodyKey] at member
    rcases (extend_seen _ _ _ _).mp member with same | previous
    · exact bodyApart (diagonalParts bodyEntry.identity entry.identity bodyEntry.identity same.symm).2.symm
    · rw [sourceDomainKey] at previous
      rcases (extend_seen _ _ _ _).mp previous with same | empty
      · exact bodyApart (diagonalParts entry.identity patternId bodyEntry.identity same.symm).1.symm
      · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at empty
  have sourceRows : InternedEdgeResidency.nodeEdges body = bodyRows := by
    rw [bodyShape]
    rfl
  have compiler : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = bodyFirst.1.key →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (InternedEdgeResidency.nodeEdges body) (InternedEdgeResidency.nodeEdges body) := by
    intro actualDomain sameKey
    have fresh : pair bodyEntry.identity bodyEntry.identity ∉ actualDomain.key.seen := by
      rw [sameKey]
      exact freshBodyPair
    have shaped : decision actualDomain.key
        (.node bodyEntry bodyRows 0 [.interned entry.identity])
        (.node bodyEntry bodyRows 0 [.interned entry.identity]) = .ordinary := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
        Value.referenceOf, Value.free, fresh]
    have literalCompiled : compileNode ⟨actualDomain,
        .node bodyEntry bodyRows 0 [.interned entry.identity],
        .node bodyEntry bodyRows 0 [.interned entry.identity]⟩ = compileRows actualDomain bodyRows bodyRows := by
      simp only [compileNode, shaped]
    calc
      compileNode ⟨actualDomain, body, body⟩ = compileNode ⟨actualDomain,
          .node bodyEntry bodyRows 0 [.interned entry.identity],
          .node bodyEntry bodyRows 0 [.interned entry.identity]⟩ :=
        congrArg (fun value : Value Symbol Guard => compileNode ⟨actualDomain, value, value⟩) bodyShape
      _ = compileRows actualDomain bodyRows bodyRows := literalCompiled
      _ = compileRows actualDomain (InternedEdgeResidency.nodeEdges body)
          (InternedEdgeResidency.nodeEdges body) := by rw [sourceRows]
  have selected : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = bodyFirst.1.key →
      decision actualDomain.key universeValue referenceValue = .leftMu := by
    intro actualDomain sameKey
    rw [sameKey]
    exact sourceFacts.1
  have childPure : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = bodyFirst.1.key →
      ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current actualDomain.key
        universeValue referenceValue entry.identity entry.identity).1,
        SourceRecursiveIntersectionKernel.body universeValue,
        SourceRecursiveIntersectionKernel.body referenceValue⟩ =
        .pure (repeatedValue (pair bodyEntry.identity entry.identity)) := by
    intro actualDomain sameKey current currentValid
    rw [sameKey]
    exact (sourceFacts.2.2.2.1 current currentValid).2.2
  have absent : let binder := pair entry.identity entry.identity
      Reference.intersection binder.1 binder.2 ∉
        (repeatedValue (pair bodyEntry.identity entry.identity) : Value Symbol Guard).free :=
    sourceFacts.2.2.1
  have read : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = bodyFirst.1.key →
      ∀ current : SourceEqualityNativeDemand.State width,
      SourceCurrentAllocatedNativePhysicalCache.Valid current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨actualDomain, referenceValue, referenceValue⟩)) current =
        .yielded (.code (requestNode actualDomain universeValue referenceValue)) current := by
    intro actualDomain sameKey current physical currentGrowth
    have bound : entry.identity ∈ names actualDomain.key := by
      rw [sameKey]
      exact readFacts.1
    have referenceSelected : decision actualDomain.key referenceValue referenceValue = .leftReference := by
      rw [sameKey]
      exact readFacts.2.1
    have compiled : compileNode ⟨actualDomain, referenceValue, referenceValue⟩ =
        compileReference actualDomain entry.identity referenceValue true :=
      reference_code actualDomain entry.identity referenceSelected
    have sourceRead : SourcePreparedSharedRows.read current.native.machine.heap entry.identity =
        some universeValue := (readFacts.2.2.2 current physical.machine.1 currentGrowth).1
    exact (congrArg (fun code : Code Symbol Guard (Value Symbol Guard) =>
      SourceEqualityNativeDemand.step (.code code) current) compiled).trans
        (reference_read_step actualDomain entry.identity referenceValue universeValue current bound sourceRead)
  have names : (SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst =
      [entry.identity] := by
    simp only [bodyShape, universeValue, SourceRecursiveIntersectionEnvironment.bindings,
      SourceRecursiveIntersectionEnvironment.binder, List.nil_append, List.map_cons, List.map_nil]
  have bodyFirstKey : bodyFirst.1.key =
      extend oldDomain.key [entry.identity] (pair bodyEntry.identity entry.identity) := by
    have normalized : bodyFirst.1.key = extend sourceDomain.1.key [entry.identity]
        (pair bodyEntry.identity entry.identity) :=
      bodyKey.trans (congrArg
        (fun bindings => extend sourceDomain.1.key bindings (pair bodyEntry.identity entry.identity)) names)
    exact normalized.trans (congrArg
      (fun currentDomain => extend currentDomain [entry.identity] (pair bodyEntry.identity entry.identity))
      (congrArg (fun currentDomain => currentDomain.key) domainEq).symm)
  have atReaderOperations := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    fuel wholeCount (.code (.node oldRoot .pure)) readerControl .pure initialState reader sourceHeap
    initialPhysical inputs fields operationsValid sourceGrowth
    (by simpa only [Control.bind_pure] using wholeActual.steps) wholeBound
  have beforeNodes : Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
      entry.identity bodyEntry.identity bodyFirst.1.key body universeValue) reader.native.nodes := by
    simpa only [bodyFirstKey, sameKey] using inherited.1
  have beforeEdges : Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
      entry.identity bodyEntry.identity bodyFirst.1.key universeValue) reader.native.edges := by
    simpa only [bodyFirstKey, sameKey] using inherited.2.1
  have laws := SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.query_returned_and_raw_results
    (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyFirst.1.key bodyEntry.identity compiler selected childPure absent read newFuel
  have result := laws.1 newRequest reader atReaderOperations.2.1 atReaderOperations.2.2.2.1
    atReaderOperations.2.2.2.2.1 newInputs newFields beforeNodes beforeEdges
  simpa only [bodyFirstKey, sameKey] using result

private theorem coherent_next_query
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel wholeCount : Nat) (readerControl : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) readerControl reader)
    (fullPattern : Value Symbol Guard) (patternId : Nat)
    (oldDomain newDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntry (width := width) oldRoot machine operations wholeCount
      entry body depth ordinary fullPattern patternId oldDomain)
    (sameKey : newDomain.key = oldDomain.key)
    (inputs : InputsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (newRequest : NodeRequest Symbol Guard) (newFuel : Nat)
    (newInputs : InputsThrough newFuel (.code (.node newRequest .pure)) reader)
    (newFields : FieldsThrough newFuel (.code (.node newRequest .pure)) reader) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let firstKey := extend newDomain.key [entry.identity] (pair entry.identity entry.identity)
    let selectedKey := extend firstKey [entry.identity] (pair bodyId entry.identity)
    (Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity selectedKey firstKey body universeValue)
        (execute newFuel (.code (.node newRequest .pure)) reader).state.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult
        (execute newFuel (.code (.node newRequest .pure)) reader).state.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (final : Checked width), count ≤ newFuel →
      Steps count (.code (.node newRequest .pure)) reader (.code (.pure value)) final →
      SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity selectedKey firstKey body universeValue newRequest value) := by
  have inherited :=
    SourceCurrentAllocatedNativePastEntryInnerPayloadTransport.inner_payloads_of_past_authentic_entry_at_equal_key
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity oldRoot machine machineValid sourceGrowth operations operationsValid
      fuel wholeCount readerControl reader wholeBound wholeActual fullPattern patternId
      oldDomain newDomain authentic sameKey inputs fields
      wholeCount readerControl reader (Nat.le_refl _) wholeActual
  have initialPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have readerResources := SourceCurrentNativeEnterCommonOperand.checked_trace_extension wholeActual initialPhysical
  have readerGrowth : Grows sourceHeap reader.native.machine.heap :=
    InternedConstructorTemplates.grows_trans sourceGrowth readerResources.2.heap
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed,
      entryBefore, entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, _allocatedEq, _entryOne, domainEq⟩ := entryData
  let universeValue : Node := .mu entry body depth ordinary
  let referenceValue : Node := .reference (.interned entry.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue fullPattern entry.identity patternId
  change oldDomain = original.1 at domainEq
  have entryTotal : entryUsed + (wholeCount - entryUsed) = wholeCount := by omega
  have wholeForEntry : Trace (entryUsed + (wholeCount - entryUsed)) (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) readerControl reader := by
    simpa only [entryTotal] using wholeActual
  have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split entryPrefix.steps wholeForEntry
  have entryPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension entrySplit.1 initialPhysical).1
  have entryLength : (wholeCount - entryUsed - 1) + 1 = wholeCount - entryUsed := by omega
  have entryActual : Trace ((wholeCount - entryUsed - 1) + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then universeValue else fullPattern)
        (if universeFirst then fullPattern else universeValue)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) entryNext)) entryBefore readerControl reader := by
    simpa only [entryLength] using entrySplit.2
  have entryReceipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary fullPattern patternClosed patternId patternIdentity patternKind universeFirst
    entryNext (wholeCount - entryUsed - 1) entryBefore reader readerControl entryPhysical entryActual
  obtain ⟨_sameAllocation, _entryStep, _checkedEntry, _entryTail, _sameHeap, _sameDomains,
      _sameOperations, _universeBefore, _patternBefore, _universeReader, patternReader,
      _entryDomain, _readerDomain, _originalKey, _nonempty, _readerPhysical,
      _entryExtension, _identityAtReader⟩ := entryReceipt
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody.current_stored_universe_diagonal_first_actual_mu_body
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      reader.native.machine.heap readerResources.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.machine.2
      fullPattern patternReader patternClosed patternId patternIdentity patternKind
  obtain ⟨inputEntry, inputRows, inputShape, rowInputs⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs.current_stored_universe_diagonal_shortcut_inputs_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      reader.native.machine.heap readerResources.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.machine.2
      fullPattern patternReader patternClosed patternId patternIdentity patternKind
  obtain ⟨readEntry, readRows, readShape, sourceRead⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyReferenceRead.current_stored_universe_diagonal_first_body_reference_read_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      reader.native.machine.heap readerResources.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.machine.2
      fullPattern patternReader patternClosed patternId patternIdentity patternKind
  have sameInputEntry : inputEntry = bodyEntry := (Value.node.inj (inputShape.symm.trans bodyShape)).1
  have sameInputRows : inputRows = bodyRows := (Value.node.inj (inputShape.symm.trans bodyShape)).2.1
  subst inputEntry
  subst inputRows
  have sameReadEntry : readEntry = bodyEntry := (Value.node.inj (readShape.symm.trans bodyShape)).1
  have sameReadRows : readRows = bodyRows := (Value.node.inj (readShape.symm.trans bodyShape)).2.1
  subst readEntry
  subst readRows
  have actualBodyIdentity : identity body = some bodyEntry.identity := by
    simp only [bodyShape, identity]
  have bodyIdEq : bodyEntry.identity = bodyId :=
    Option.some.inj (actualBodyIdentity.symm.trans bodyIdentity)
  subst bodyId
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    universeValue referenceValue entry.identity entry.identity
  let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
    body universeValue bodyEntry.identity entry.identity
  let firstKey := extend oldDomain.key [entry.identity] (pair entry.identity entry.identity)
  let selectedKey := extend firstKey [entry.identity] (pair bodyEntry.identity entry.identity)
  have originalValid : Cache.Valid original.2 :=
    (IntersectionEmptyDomain.make_correct entryBefore.native.machine.domains entryPhysical.machine.2 _).1
  have diagonalValid : Cache.Valid diagonalFirst.2 :=
    (IntersectionEmptyDomain.make_correct original.2 originalValid _).1
  have diagonalKey := SourceRecursiveIntersectionSchedule.entered_key original.2 originalValid original.1.key
    universeValue referenceValue entry.identity entry.identity
  change diagonalFirst.1.key = extend original.1.key [entry.identity]
    (pair entry.identity entry.identity) at diagonalKey
  have firstKeyEq : diagonalFirst.1.key = firstKey := by
    rw [diagonalKey, ← domainEq]
  have terminalKey := SourceRecursiveIntersectionSchedule.entered_key diagonalFirst.2 diagonalValid diagonalFirst.1.key
    body universeValue bodyEntry.identity entry.identity
  change diagonalTerminal.1.key = extend diagonalFirst.1.key
    ((SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst)
    (pair bodyEntry.identity entry.identity) at terminalKey
  have names : (SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst = [entry.identity] := by
    rw [bodyShape]
    rfl
  have selectedKeyEq : diagonalTerminal.1.key = selectedKey := by
    rw [terminalKey, names, firstKeyEq]
  dsimp only at sourceFacts rowInputs sourceRead
  obtain ⟨_sourceIdentity, _universeIdentity, _bodyOpen, cutoffApart, incomingFacts, terminalFacts⟩ := sourceFacts
  have compiler : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (InternedEdgeResidency.nodeEdges body) (InternedEdgeResidency.nodeEdges body) := by
    intro actualDomain sameKey
    exact (terminalFacts actualDomain (sameKey.trans selectedKeyEq.symm)).2.2
  have sourceRows : InternedEdgeResidency.nodeEdges body = bodyRows := by
    rw [bodyShape]
    rfl
  have orderedInputs : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey → ∀ row ∈ InternedEdgeResidency.nodeEdges body,
      All₂ (fun (children : Node × Node) (value : Node) => KnownResult ⟨actualDomain, children.1, children.2⟩ value)
        (row.children.zip row.children)
        (row.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (pair entry.identity entry.identity))))) := by
    intro actualDomain sameKey row member
    exact rowInputs actualDomain (sameKey.trans selectedKeyEq.symm) row (by rw [← sourceRows]; exact member)
  have rightMu : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = firstKey → decision actualDomain.key body universeValue = .rightMu := by
    intro actualDomain sameKey
    exact (incomingFacts actualDomain (sameKey.trans firstKeyEq.symm)).1
  have childKey : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = firstKey →
      ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      (SourceRecursiveIntersectionEnvironment.enter current actualDomain.key body universeValue
        bodyEntry.identity entry.identity).1.key = selectedKey := by
    intro actualDomain sameKey current currentValid
    exact ((incomingFacts actualDomain (sameKey.trans firstKeyEq.symm)).2.2 current currentValid).trans selectedKeyEq
  have pairedApart : pair bodyEntry.identity entry.identity ≠ pair entry.identity entry.identity :=
    fun same => cutoffApart same.symm
  have read : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = firstKey → ∀ current : Checked width, Physical current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step (.code (compileNode ⟨actualDomain, body, referenceValue⟩)) current =
        .yielded (.code (requestNode actualDomain body universeValue)) current := by
    intro actualDomain sameKey current physical growth
    exact ((sourceRead actualDomain (sameKey.trans firstKeyEq.symm)).2.2.2.2 current physical.machine.1 growth).2
  let initialState : Checked width := ⟨initial width machine, operations⟩
  have atReaderOperations := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    fuel wholeCount (.code (.node oldRoot .pure)) readerControl .pure initialState reader sourceHeap
    initialPhysical inputs fields operationsValid sourceGrowth
    (by simpa only [Control.bind_pure] using wholeActual.steps) wholeBound
  have beforeNodes : Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
      entry.identity entry.identity entry.identity selectedKey firstKey body universeValue)
      reader.native.nodes := by
    simpa only [sameKey, selectedKey, firstKey] using inherited.2.2.1
  have laws := SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.query_returned_and_raw_results
    (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    selectedKey entry.identity entry.identity compiler orderedInputs firstKey bodyEntry.identity
    rightMu actualBodyIdentity childKey pairedApart read newFuel
  have result := laws.1 newRequest reader atReaderOperations.2.1 atReaderOperations.2.2.2.1
    atReaderOperations.2.2.2.2.1 newInputs newFields beforeNodes inherited.2.2.2
  simpa only [sameKey, selectedKey, firstKey] using result

theorem next_node_query_preserves_actual_past_inner_payloads
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel wholeCount : Nat) (readerControl : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) readerControl reader)
    (fullPattern : Value Symbol Guard) (patternId : Nat)
    (oldDomain newDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntry (width := width) oldRoot machine operations wholeCount
      entry body depth ordinary fullPattern patternId oldDomain)
    (sameKey : newDomain.key = oldDomain.key)
    (inputs : InputsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (newRequest : NodeRequest Symbol Guard) (newFuel : Nat)
    (newInputs : InputsThrough newFuel (.code (.node newRequest .pure)) reader)
    (newFields : FieldsThrough newFuel (.code (.node newRequest .pure)) reader) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let bodyFirst := extend newDomain.key [entry.identity] (pair bodyId entry.identity)
    let diagonalFirst := extend newDomain.key [entry.identity] (pair entry.identity entry.identity)
    let diagonalTerminal := extend diagonalFirst [entry.identity] (pair bodyId entry.identity)
    let after := (execute newFuel (.code (.node newRequest .pure)) reader).state
    (Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId bodyFirst body universeValue) after.native.nodes ∧
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
        entry.identity bodyId bodyFirst universeValue) after.native.edges ∧
      Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue)
        after.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult after.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (final : Checked width), count ≤ newFuel →
      Steps count (.code (.node newRequest .pure)) reader (.code (.pure value)) final →
      SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId bodyFirst body universeValue newRequest value ∧
      SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue newRequest value) := by
  have bodyFirst := body_first_next_query
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity oldRoot machine machineValid sourceGrowth operations operationsValid
    fuel wholeCount readerControl reader wholeBound wholeActual fullPattern patternId
    oldDomain newDomain authentic sameKey inputs fields newRequest newFuel newInputs newFields
  have coherent := coherent_next_query
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity oldRoot machine machineValid sourceGrowth operations operationsValid
    fuel wholeCount readerControl reader wholeBound wholeActual fullPattern patternId
    oldDomain newDomain authentic sameKey inputs fields newRequest newFuel newInputs newFields
  dsimp only at bodyFirst coherent ⊢
  refine ⟨⟨bodyFirst.1.1, bodyFirst.1.2, coherent.1.1, coherent.1.2⟩, ?_⟩
  intro count value final bounded actual
  exact ⟨bodyFirst.2 count value final bounded actual, coherent.2 count value final bounded actual⟩

end MicroCFTA.SourceCurrentAllocatedNativePastEntryNextQueryInnerLaws
