import MicroCFTA.SourceCurrentNativeWarmBodyFirstInitialPayloads
import MicroCFTA.SourceCurrentNativeWarmCoherentInitialPayloads
import MicroCFTA.SourceCurrentAllocatedNativePrefixOperations
import MicroCFTA.SourceEqualityNativeDemandContinuation

namespace MicroCFTA.SourceCurrentNativeWarmAuxiliaryPrefixes
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedEdgeResidency (nodeEdges)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (KnownResult)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
set_option autoImplicit false

/- Note [Fixed full history at earlier warm prefixes]
The full new history qualifies the later source entry.
The actual prefix count controls only the existing family executor.
Public initial seeds supply both old memo laws for each source family.
Uniform source callbacks preserve them through the actual warm writes.
The proof derives all reached physical and operation facts from original plans.
-/

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

theorem auxiliary_payloads_at_every_actual_warm_prefix
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
    (oldRootDomain : oldRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (oldRootClosed : oldRoot.left.free = [] ∧ oldRoot.right.free = [])
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (oldFuel oldCount : Nat) (oldControl : Control (Value Symbol Guard))
    (oldSnapshot : Checked width) (oldBound : oldCount ≤ oldFuel)
    (oldInputs : InputsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldFields : FieldsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldActual : Trace oldCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) oldControl oldSnapshot)
    (newRoot : NodeRequest Symbol Guard) (newFuel newCount : Nat)
    (newControl : Control (Value Symbol Guard)) (warmReader : Checked width)
    (newBound : newCount ≤ newFuel)
    (newInputs : InputsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (newFields : FieldsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (newActual : Trace newCount (.code (.node newRoot .pure))
      oldSnapshot newControl warmReader) :
    ∀ (prefixCount : Nat) (prefixControl : Control (Value Symbol Guard)) (current : Checked width),
      prefixCount ≤ newCount →
      Trace prefixCount (.code (.node newRoot .pure)) oldSnapshot prefixControl current →
      ∀ (pattern : Value Symbol Guard) (patternId : Nat)
        (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
        SourceCurrentAllocatedNativeSourceWarmEntry.AuthenticEntryAt (width := width)
          newRoot oldSnapshot newCount entry body depth ordinary pattern patternId domain →
        let universeValue : Value Symbol Guard := .mu entry body depth ordinary
        let bodyFirst := extend domain.key [entry.identity] (pair bodyId entry.identity)
        let diagonalFirst := extend domain.key [entry.identity] (pair entry.identity entry.identity)
        let diagonalTerminal := extend diagonalFirst [entry.identity] (pair bodyId entry.identity)
        Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
          entry.identity bodyId bodyFirst body universeValue) current.native.nodes ∧
        Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
          entry.identity bodyId bodyFirst universeValue) current.native.edges ∧
        Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
          entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue)
          current.native.nodes ∧
        Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult current.native.edges
 := by
  have inheritedBodyFirst :=
    SourceCurrentNativeWarmBodyFirstInitialPayloads.body_first_initial_payloads_for_actual_warm_history
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth
      operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
      newRoot newFuel newCount newControl warmReader newBound newInputs newFields newActual
  have inheritedCoherent :=
    SourceCurrentNativeWarmCoherentInitialPayloads.coherent_initial_payloads_for_actual_warm_history
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth
      operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
      newRoot newFuel newCount newControl warmReader newBound newInputs newFields newActual
  intro prefixCount prefixControl current prefixBound prefixActual pattern patternId domain authentic
  have beforeBodyFirst := inheritedBodyFirst pattern patternId domain authentic
  have beforeCoherent := inheritedCoherent pattern patternId domain authentic
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let coldInitial : Checked width := ⟨initial width machine, operations⟩
  let warmRootControl : Control (Value Symbol Guard) := .code (.node newRoot .pure)
  have initialPhysical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid
  have atOld := SourceCurrentNativeEnterCommonOperand.checked_trace_extension oldActual initialPhysical
  have atReader := SourceCurrentNativeEnterCommonOperand.checked_trace_extension newActual atOld.1
  have readerGrowth : Grows sourceHeap warmReader.native.machine.heap :=
    InternedConstructorTemplates.grows_trans sourceGrowth
      (InternedConstructorTemplates.grows_trans atOld.2.heap atReader.2.heap)
  have oldOperations := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    oldFuel oldCount (.code (.node oldRoot .pure)) oldControl .pure coldInitial oldSnapshot sourceHeap
    initialPhysical oldInputs oldFields operationsValid sourceGrowth
    (by simpa only [Control.bind_pure] using oldActual.steps) oldBound
  have prefixPlan := SourceCurrentAllocatedNativeSourceQueryInduction.through_mono
    newFuel prefixCount warmRootControl oldSnapshot (by omega) newInputs
  have prefixFields := SourceCurrentAllocatedNativeSourceQueryInduction.fields_mono
    newFuel prefixCount warmRootControl oldSnapshot (by omega) newFields
  have prefixExecution := prefixActual.steps.execute
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
  have entryTotal : entryUsed + (newCount - entryUsed) = newCount := by omega
  have entryWhole : Trace (entryUsed + (newCount - entryUsed)) warmRootControl oldSnapshot newControl warmReader :=
    entryTotal.symm ▸ newActual
  have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split entryPrefix.steps entryWhole
  have entryPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension entrySplit.1 atOld.1
  have entryLength : newCount - entryUsed = (newCount - entryUsed - 1) + 1 := by omega
  have entryActual : Trace ((newCount - entryUsed - 1) + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext))
      entryBefore newControl warmReader := entryLength ▸ entrySplit.2
  obtain ⟨_entryStep, _entryTail, _entryHeap, _entryDomains, _entryOperations, _oldDomain,
    _leftAtEntry, _rightAtEntry, leftReader, rightReader, _domainAfterEntry, _domainAtReader,
    _enteredKey, _entryExtension, _sameRecord⟩ :=
    SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
      IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext
      (newCount - entryUsed - 1) entryBefore warmReader newControl entryPhysical.1 entryActual
  have patternReader : Available warmReader.native.machine.heap pattern := by
    cases universeFirst with
    | false => exact leftReader
    | true => exact rightReader
  obtain ⟨bodyEntry, bodyRows, bodyShape, bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      warmReader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
  obtain ⟨readEntry, readRows, readShape, readFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstReferenceRead.current_stored_universe_body_first_reference_read
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      warmReader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
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
      ((SourceRecursiveIntersectionEnvironment.bindings universeValue pattern).map Prod.fst)
      (pair entry.identity patternId) :=
    SourceRecursiveIntersectionSchedule.entered_key entryBefore.native.machine.domains entryPhysical.1.machine.2 IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
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
      extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity) := by
    have normalized : bodyFirst.1.key = extend sourceDomain.1.key [entry.identity]
        (pair bodyEntry.identity entry.identity) :=
      bodyKey.trans (congrArg
        (fun bindings => extend sourceDomain.1.key bindings (pair bodyEntry.identity entry.identity)) names)
    exact normalized.trans (congrArg
      (fun currentDomain => extend currentDomain [entry.identity] (pair bodyEntry.identity entry.identity))
      (congrArg (fun currentDomain => currentDomain.key) domainEq).symm)
  have beforeBodyFirstNodes : Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
      entry.identity bodyEntry.identity bodyFirst.1.key body universeValue) oldSnapshot.native.nodes := by
    simpa only [bodyFirstKey] using beforeBodyFirst.1
  have beforeBodyFirstEdges : Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
      entry.identity bodyEntry.identity bodyFirst.1.key universeValue) oldSnapshot.native.edges := by
    simpa only [bodyFirstKey] using beforeBodyFirst.2
  have bodyFirstLaws := SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.query_returned_and_raw_results
    (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyFirst.1.key bodyEntry.identity compiler selected childPure absent read prefixCount
  have bodyFirstRun := bodyFirstLaws.1 newRoot oldSnapshot oldOperations.2.1 oldOperations.2.2.2.1
    oldOperations.2.2.2.2.1 prefixPlan prefixFields beforeBodyFirstNodes beforeBodyFirstEdges
  have bodyFirstAtCurrent :
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyEntry.identity (extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity))
        body universeValue) current.native.nodes ∧
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
        entry.identity bodyEntry.identity (extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity))
        universeValue) current.native.edges := by
    have result := bodyFirstRun.1
    rw [prefixExecution] at result
    simpa only [Outcome.state, bodyFirstKey] using result
  obtain ⟨diagonalBodyEntry, diagonalBodyRows, diagonalBodyShape, _bodyApart, diagonalSourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody.current_stored_universe_diagonal_first_actual_mu_body
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      warmReader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
  obtain ⟨inputEntry, inputRows, inputShape, rowInputs⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs.current_stored_universe_diagonal_shortcut_inputs_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      warmReader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
  obtain ⟨diagonalReadEntry, diagonalReadRows, diagonalReadShape, diagonalSourceRead⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyReferenceRead.current_stored_universe_diagonal_first_body_reference_read_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      warmReader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
  have sameInputEntry : inputEntry = diagonalBodyEntry := (Value.node.inj (inputShape.symm.trans diagonalBodyShape)).1
  have sameInputRows : inputRows = diagonalBodyRows := (Value.node.inj (inputShape.symm.trans diagonalBodyShape)).2.1
  subst inputEntry
  subst inputRows
  have sameReadEntry : diagonalReadEntry = diagonalBodyEntry := (Value.node.inj (diagonalReadShape.symm.trans diagonalBodyShape)).1
  have sameReadRows : diagonalReadRows = diagonalBodyRows := (Value.node.inj (diagonalReadShape.symm.trans diagonalBodyShape)).2.1
  subst diagonalReadEntry
  subst diagonalReadRows
  have sameDiagonalEntry : diagonalBodyEntry = bodyEntry :=
    (Value.node.inj (diagonalBodyShape.symm.trans bodyShape)).1
  have sameDiagonalRows : diagonalBodyRows = bodyRows :=
    (Value.node.inj (diagonalBodyShape.symm.trans bodyShape)).2.1
  subst diagonalBodyEntry
  subst diagonalBodyRows
  have actualBodyIdentity : identity body = some bodyEntry.identity := by
    simp only [bodyShape, identity]
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
    universeValue referenceValue entry.identity entry.identity
  let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
    body universeValue bodyEntry.identity entry.identity
  let firstKey := extend domain.key [entry.identity] (pair entry.identity entry.identity)
  let selectedKey := extend firstKey [entry.identity] (pair bodyEntry.identity entry.identity)
  have originalValid : Cache.Valid sourceDomain.2 :=
    (IntersectionEmptyDomain.make_correct entryBefore.native.machine.domains entryPhysical.1.machine.2 _).1
  have diagonalValid : Cache.Valid diagonalFirst.2 :=
    (IntersectionEmptyDomain.make_correct sourceDomain.2 originalValid _).1
  have diagonalKey := SourceRecursiveIntersectionSchedule.entered_key sourceDomain.2 originalValid sourceDomain.1.key
    universeValue referenceValue entry.identity entry.identity
  change diagonalFirst.1.key = extend sourceDomain.1.key [entry.identity]
    (pair entry.identity entry.identity) at diagonalKey
  have firstKeyEq : diagonalFirst.1.key = firstKey := by
    rw [diagonalKey, ← domainEq]
  have terminalKey := SourceRecursiveIntersectionSchedule.entered_key diagonalFirst.2 diagonalValid diagonalFirst.1.key
    body universeValue bodyEntry.identity entry.identity
  change diagonalTerminal.1.key = extend diagonalFirst.1.key
    ((SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst)
    (pair bodyEntry.identity entry.identity) at terminalKey
  have names : (SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst = [entry.identity] := by
    rw [diagonalBodyShape]
    rfl
  have selectedKeyEq : diagonalTerminal.1.key = selectedKey := by
    rw [terminalKey, names, firstKeyEq]
  dsimp only at diagonalSourceFacts rowInputs diagonalSourceRead
  obtain ⟨_sourceIdentity, _universeIdentity, _bodyOpen, cutoffApart, incomingFacts, terminalFacts⟩ := diagonalSourceFacts
  have compiler : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (InternedEdgeResidency.nodeEdges body) (InternedEdgeResidency.nodeEdges body) := by
    intro actualDomain sameKey
    exact (terminalFacts actualDomain (sameKey.trans selectedKeyEq.symm)).2.2
  have sourceRows : InternedEdgeResidency.nodeEdges body = bodyRows := by
    rw [diagonalBodyShape]
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
    exact ((diagonalSourceRead actualDomain (sameKey.trans firstKeyEq.symm)).2.2.2.2 current physical.machine.1 growth).2
  have beforeCoherentNodes : Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
      entry.identity entry.identity entry.identity selectedKey firstKey body universeValue)
      oldSnapshot.native.nodes := by
    exact beforeCoherent.1
  have coherentLaws := SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.query_returned_and_raw_results
    (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    selectedKey entry.identity entry.identity compiler orderedInputs firstKey bodyEntry.identity
    rightMu actualBodyIdentity childKey pairedApart read prefixCount
  have coherentRun := coherentLaws.1 newRoot oldSnapshot oldOperations.2.1 oldOperations.2.2.2.1
    oldOperations.2.2.2.2.1 prefixPlan prefixFields beforeCoherentNodes beforeCoherent.2
  have coherentAtCurrent := coherentRun.1
  rw [prefixExecution] at coherentAtCurrent
  exact ⟨bodyFirstAtCurrent.1, bodyFirstAtCurrent.2, coherentAtCurrent.1, coherentAtCurrent.2⟩

end MicroCFTA.SourceCurrentNativeWarmAuxiliaryPrefixes
