import MicroCFTA.SourceCurrentAllocatedNativeAuthenticCoherentInnerHistory
import MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry

/- Note [Coherent initial laws for a later warm entry]
The new actual entry supplies structural source facts at its common reader.
The compiler callbacks quantify over all matching handles and grown heaps.
The existing cold initializer uses these callbacks at the old budget.
It returns both initial memo laws for the same old snapshot.
No old entry, future cache meaning, or model is a premise.
-/
namespace MicroCFTA.SourceCurrentNativeWarmCoherentInitialPayloads
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (KnownResult)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

theorem coherent_initial_payloads_for_actual_warm_history
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
    ∀ (pattern : Value Symbol Guard) (patternId : Nat)
      (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
      SourceCurrentAllocatedNativeSourceWarmEntry.AuthenticEntryAt (width := width)
        newRoot oldSnapshot newCount entry body depth ordinary pattern patternId domain →
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let firstKey := extend domain.key [entry.identity] (pair entry.identity entry.identity)
      let selectedKey := extend firstKey [entry.identity] (pair bodyId entry.identity)
      Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity selectedKey firstKey body universeValue)
        oldSnapshot.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult oldSnapshot.native.edges
 := by
  have _ := oldRootDomain
  have _ := oldRootClosed
  have _ := newBound
  have _ := newInputs
  have _ := newFields
  intro pattern patternId domain authentic
  have initialPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have oldResources := SourceCurrentNativeEnterCommonOperand.checked_trace_extension oldActual initialPhysical
  have readerResources := SourceCurrentNativeEnterCommonOperand.checked_trace_extension newActual oldResources.1
  have oldGrowth : Grows sourceHeap oldSnapshot.native.machine.heap :=
    InternedConstructorTemplates.grows_trans sourceGrowth oldResources.2.heap
  have readerGrowth : Grows sourceHeap warmReader.native.machine.heap :=
    InternedConstructorTemplates.grows_trans oldGrowth readerResources.2.heap
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed,
      entryBefore, entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, _allocatedEq, _entryOne, domainEq⟩ := entryData
  let universeValue : Node := .mu entry body depth ordinary
  let referenceValue : Node := .reference (.interned entry.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  change domain = original.1 at domainEq
  have entryTotal : entryUsed + (newCount - entryUsed) = newCount := by omega
  have wholeForEntry : Trace (entryUsed + (newCount - entryUsed)) (.code (.node newRoot .pure))
      oldSnapshot newControl warmReader := by
    simpa only [entryTotal] using newActual
  have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split entryPrefix.steps wholeForEntry
  have entryPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension entrySplit.1 oldResources.1).1
  have entryLength : (newCount - entryUsed - 1) + 1 = newCount - entryUsed := by omega
  have entryActual : Trace ((newCount - entryUsed - 1) + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then universeValue else pattern)
        (if universeFirst then pattern else universeValue)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) entryNext)) entryBefore newControl warmReader := by
    simpa only [entryLength] using entrySplit.2
  have entryReceipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary pattern patternClosed patternId patternIdentity patternKind universeFirst
    entryNext (newCount - entryUsed - 1) entryBefore warmReader newControl entryPhysical entryActual
  obtain ⟨_sameAllocation, _entryStep, _checkedEntry, _entryTail, _sameHeap, _sameDomains,
      _sameOperations, _universeBefore, _patternBefore, _universeReader, patternReader,
      _entryDomain, _readerDomain, _originalKey, _nonempty, _readerPhysical,
      _entryExtension, _identityAtReader⟩ := entryReceipt
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody.current_stored_universe_diagonal_first_actual_mu_body
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      warmReader.native.machine.heap readerResources.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
  obtain ⟨inputEntry, inputRows, inputShape, rowInputs⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs.current_stored_universe_diagonal_shortcut_inputs_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      warmReader.native.machine.heap readerResources.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
  obtain ⟨readEntry, readRows, readShape, sourceRead⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyReferenceRead.current_stored_universe_diagonal_first_body_reference_read_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      warmReader.native.machine.heap readerResources.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
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
  let firstKey := extend domain.key [entry.identity] (pair entry.identity entry.identity)
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
  have prefixInputs := SourceCurrentAllocatedNativeSourceQueryInduction.through_mono
    oldFuel oldCount (.code (.node oldRoot .pure)) (⟨initial width machine, operations⟩ : Checked width)
    oldBound oldInputs
  have prefixFields := SourceCurrentAllocatedNativeSourceQueryInduction.fields_mono
    oldFuel oldCount (.code (.node oldRoot .pure)) (⟨initial width machine, operations⟩ : Checked width)
    oldBound oldFields
  have completed := SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.initial_node_query_returned_and_raw_results
    (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    selectedKey entry.identity entry.identity compiler orderedInputs firstKey bodyEntry.identity
    rightMu actualBodyIdentity childKey pairedApart read
    machine machineValid sourceGrowth operations operationsValid oldCount oldRoot prefixInputs prefixFields
  have retained := completed.1
  have prefixExecution := oldActual.steps.execute
  rw [prefixExecution] at retained
  exact retained

end MicroCFTA.SourceCurrentNativeWarmCoherentInitialPayloads
