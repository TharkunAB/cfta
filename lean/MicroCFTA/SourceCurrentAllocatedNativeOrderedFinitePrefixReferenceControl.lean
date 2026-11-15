import MicroCFTA.SourceCurrentNativeOrderedOriginalEntry
import MicroCFTA.SourceCurrentAllocatedNativeCommonReaderReferenceControl
import MicroCFTA.SourceEqualityNativeDemandPrefixSplit

/-!
# Reference control at a finite actual prefix

The actual trace supplies both reader suffixes.
The entry has occurred before the observed endpoint.
The original pattern and its height bound stay fixed.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeOrderedFinitePrefixReferenceControl
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisUniversePrefixHeight (height)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeMixedReferenceControl

set_option autoImplicit false
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

private theorem checked_split_at_raw_prefix
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {Output : Type}
    {wholeCount prefixCount : Nat} {initial middle final : Control Output}
    {start current reader : Checked width}
    (whole : Trace wholeCount initial start final reader)
    (prefixActual : Steps prefixCount initial start middle current)
    (bounded : prefixCount ≤ wholeCount) :
    Trace prefixCount initial start middle current ∧
      Trace (wholeCount - prefixCount) middle current final reader := by
  induction prefixActual generalizing wholeCount final reader with
  | refl =>
      exact ⟨.refl _ _, by simpa only [Nat.sub_zero] using whole⟩
  | cons control state next reached middle current count one tail ih =>
      cases whole with
      | refl => omega
      | cons _ _ other advanced _ _ remaining inputs first rest =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
          obtain ⟨checkedPrefix, checkedSuffix⟩ := ih rest (by omega)
          refine ⟨.cons control state next reached middle current count inputs one checkedPrefix, ?_⟩
          have lengthEq : remaining + 1 - (count + 1) = remaining - count := by omega
          simpa only [lengthEq] using checkedSuffix

/-- The same actual finite trace supplies either ordered original entry and both reference controls. -/
theorem current_stored_universe_ref_control_at_finite_prefix_ordered_entry
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
    (patternKind : tag pattern = 1 ∨ tag pattern = 3) (universeFirst : Bool)
    (initial : Control Output) (start entryBefore before reader : Checked width)
    (startPhysical : Physical start.native)
    (growth : Grows sourceHeap start.native.machine.heap)
    (wholeCount entryCount producerCount : Nat) (final : Control Output)
    (wholeActual : Trace wholeCount initial start final reader)
    (entryStrict : entryCount < wholeCount) (producerBound : producerCount ≤ wholeCount)
    (entryNext : Interned DomainKey → Code Symbol Guard Output)
    (entryPrefix : Steps entryCount initial start
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then .mu entry body depth ordinary else pattern)
        (if universeFirst then pattern else .mu entry body depth ordinary)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) entryNext)) entryBefore)
    (operand : Node) (operandAvailable : Available before.native.machine.heap operand)
    (operandClosed : operand.free = []) (smaller : height operand < height pattern)
    (referenceFirst : Bool) (next : Node → Code Symbol Guard Output)
    (producerPrefix :
      let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
        IntersectionEmptyDomain.emptyKey (.mu entry body depth ordinary) pattern entry.identity patternId
      Steps producerCount initial start (.code ((compileNode ⟨entered.1,
        if referenceFirst then .reference (.interned entry.identity) else operand,
        if referenceFirst then operand else .reference (.interned entry.identity)⟩).bind next)) before) :
    let universeValue : Node := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    entryCount ≤ wholeCount ∧ producerCount ≤ wholeCount ∧
    Trace entryCount initial start
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then universeValue else pattern)
        (if universeFirst then pattern else universeValue)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) entryNext)) entryBefore ∧
    Trace (wholeCount - entryCount)
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then universeValue else pattern)
        (if universeFirst then pattern else universeValue)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) entryNext)) entryBefore final reader ∧
    Trace producerCount initial start
      (.code ((compileNode ⟨entered.1,
        if referenceFirst then .reference (.interned entry.identity) else operand,
        if referenceFirst then operand else .reference (.interned entry.identity)⟩).bind next)) before ∧
    Trace (wholeCount - producerCount)
      (.code ((compileNode ⟨entered.1,
        if referenceFirst then .reference (.interned entry.identity) else operand,
        if referenceFirst then operand else .reference (.interned entry.identity)⟩).bind next))
      before final reader ∧
    universeValue.free = [] ∧ Available before.native.machine.heap universeValue ∧
    Extension before.native.machine reader.native.machine ∧
    entry.identity ∈ names entered.1.key ∧
    lookup before.native.machine.heap entered.1.key entry.identity = some universeValue ∧
    SourcePreparedSharedRows.read before.native.machine.heap entry.identity = some universeValue ∧
    (∀ cutoff, decision entered.1.key (.reference (.interned entry.identity)) operand ≠ .repeated cutoff) ∧
    (∀ cutoff, decision entered.1.key operand (.reference (.interned entry.identity)) ≠ .repeated cutoff) ∧
    (∀ (operandEntry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (level : Nat),
      operand = .node operandEntry rows level [] →
      decision entered.1.key operand (.reference (.interned entry.identity)) = .rightReference ∧
      decision entered.1.key (.reference (.interned entry.identity)) operand = .swap ∧
      compileNode ⟨entered.1, operand, .reference (.interned entry.identity)⟩ =
        compileReference entered.1 entry.identity operand false ∧
      compileNode ⟨entered.1, .reference (.interned entry.identity), operand⟩ =
        requestNode entered.1 operand (.reference (.interned entry.identity)) ∧
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨entered.1, operand, .reference (.interned entry.identity)⟩)) before =
        .yielded (.code (requestNode entered.1 operand universeValue)) before ∧
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨entered.1, .reference (.interned entry.identity), operand⟩)) before =
        SourceEqualityNativeDemand.step
          (.code (requestNode entered.1 operand (.reference (.interned entry.identity)))) before) := by
  let universeValue : Node := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let entryControl : Control Output :=
    .code (.enter IntersectionEmptyDomain.emptyDomain
      (if universeFirst then universeValue else pattern)
      (if universeFirst then pattern else universeValue)
      (if universeFirst then entry.identity else patternId)
      (if universeFirst then patternId else entry.identity) entryNext)
  let producerControl : Control Output := .code ((compileNode ⟨entered.1,
    if referenceFirst then .reference (.interned entry.identity) else operand,
    if referenceFirst then operand else .reference (.interned entry.identity)⟩).bind next)
  have entryBound : entryCount ≤ wholeCount := Nat.le_of_lt entryStrict
  have entrySplit := checked_split_at_raw_prefix wholeActual entryPrefix entryBound
  have producerSplit := checked_split_at_raw_prefix wholeActual producerPrefix producerBound
  have entryFacts := SourceCurrentNativeEnterCommonOperand.checked_trace_extension entrySplit.1 startPhysical
  have producerFacts := SourceCurrentNativeEnterCommonOperand.checked_trace_extension producerSplit.1 startPhysical
  have physical : Physical before.native := producerFacts.1
  have beforeGrowth : Grows sourceHeap before.native.machine.heap :=
    grows_trans growth producerFacts.2.heap
  have entrySuffix : Trace (wholeCount - entryCount) entryControl entryBefore final reader := entrySplit.2
  have entryLength : wholeCount - entryCount = (wholeCount - entryCount - 1) + 1 := by omega
  have enteredActual : Trace ((wholeCount - entryCount - 1) + 1) entryControl entryBefore final reader :=
    entryLength ▸ entrySuffix
  have producerSuffix : Trace (wholeCount - producerCount) producerControl before final reader := producerSplit.2
  have receipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary pattern patternClosed patternId patternIdentity patternKind universeFirst
    entryNext (wholeCount - entryCount - 1) entryBefore reader final entryFacts.1 enteredActual
  obtain ⟨_allocatedEq, _entryStep, _entryChecked, _entryTail, _enteredHeap, _enteredDomains,
    _enteredOperations, _universeBefore, _patternBefore, _universeReader, patternReader,
    _startedDomain, _readerDomain, enteredKey, _nonempty, _readerPhysical, _entryExtension,
    _sameClosedPattern⟩ := receipt
  have later := SourceCurrentNativeEnterCommonOperand.checked_trace_extension producerSuffix physical
  have operandReader : Available reader.native.machine.heap operand :=
    later.2.available operand operandAvailable
  have universeAvailable : Available before.native.machine.heap universeValue :=
    physical.machine.1.cached.nodes key _ (beforeGrowth.nodeRecords key _ stored)
  have universeClosed : universeValue.free = [] := by
    rcases SourceSynthesisCurrentUniverseOwnership.current_build_single_universe
        lib query signed whole accepted rootValue sourceHeap built with noMu | someMu
    · exact False.elim (noMu key entry body depth ordinary stored)
    · obtain ⟨_owner, _ownerBody, _ownerDepth, _ownerOrdinary, _ownerStored, _ownerAvailable,
          ownerClosed, _ownerReplay, unique⟩ := someMu
      have same := unique key entry body depth ordinary stored
      change (Value.mu entry body depth ordinary).free = []
      rw [same]
      exact ownerClosed
  have bound : entry.identity ∈ names entered.1.key := by
    rw [enteredKey, extend_names]
    exact Or.inl List.mem_cons_self
  have found : lookup before.native.machine.heap entered.1.key entry.identity = some universeValue :=
    lookup_mu before.native.machine.heap physical.machine.1 entered.1.key entry body depth ordinary
      universeAvailable bound
  have read : SourcePreparedSharedRows.read before.native.machine.heap entry.identity = some universeValue :=
    SourcePreparedSharedRows.read_identity before.native.machine.heap physical.machine.1
      universeValue universeAvailable entry.identity rfl
  have allFresh : ∀ operandId, identity operand = some operandId →
      pair entry.identity operandId ∉ entered.1.key.seen ∧
      pair operandId entry.identity ∉ entered.1.key.seen := by
    intro operandId operandIdentity
    have different := SourceSynthesisUniverseMixedDescendantFreshness.strict_prefix_height_identity_ne
      reader.native.machine.heap later.1.machine.1 pattern operand patternReader operandReader
      patternClosed operandClosed patternId operandId patternIdentity operandIdentity smaller
    have directApart : pair entry.identity operandId ≠ pair entry.identity patternId := by
      intro same
      have lower := congrArg Prod.fst same
      have upper := congrArg Prod.snd same
      simp only [pair] at lower upper
      apply different
      omega
    have swapped : pair operandId entry.identity = pair entry.identity operandId := by
      simp only [pair, Nat.min_comm, Nat.max_comm]
    have reverseApart : pair operandId entry.identity ≠ pair entry.identity patternId :=
      fun same => directApart (swapped.symm.trans same)
    have absent : ∀ candidate, candidate ≠ pair entry.identity patternId → candidate ∉ entered.1.key.seen := by
      intro candidate differentKey member
      rw [enteredKey] at member
      rcases (extend_seen IntersectionEmptyDomain.emptyKey
        [entry.identity]
        (pair entry.identity patternId) candidate).mp member with same | old
      · exact differentKey same
      · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at old
    exact ⟨absent _ directApart, absent _ reverseApart⟩
  have notRepeated := fresh_reference_decisions entered.1 entry.identity operand allFresh
  dsimp only
  refine ⟨entryBound, producerBound, entrySplit.1, entrySplit.2, producerSplit.1, producerSplit.2,
    universeClosed, universeAvailable, later.2, bound, found, read, notRepeated.1, notRepeated.2, ?_⟩
  intro operandEntry rows level operandEq
  subst operand
  have fresh := (allFresh operandEntry.identity rfl).2
  have selected := node_reference_branch entered.1 operandEntry rows level entry.identity fresh
  have reversed := reference_node_branch entered.1 operandEntry rows level entry.identity
  have compiled : compileNode ⟨entered.1, .node operandEntry rows level [],
      .reference (.interned entry.identity)⟩ =
      compileReference entered.1 entry.identity (.node operandEntry rows level []) false := by
    simp only [compileNode, selected]
  have reverseCompiled : compileNode ⟨entered.1, .reference (.interned entry.identity),
      .node operandEntry rows level []⟩ =
      requestNode entered.1 (.node operandEntry rows level []) (.reference (.interned entry.identity)) := by
    simp only [compileNode, reversed]
  refine ⟨selected, reversed, compiled, reverseCompiled, ?_, ?_⟩
  · change SourceEqualityNativeDemand.step
        (.code (compileNode ⟨entered.1, .node operandEntry rows level [],
          .reference (.interned entry.identity)⟩)) before =
      .yielded (.code (requestNode entered.1 (.node operandEntry rows level []) universeValue)) before
    simp [compiled, compileReference, bound, SourceEqualityNativeDemand.step,
      SourceRecursiveIntersectionNative.step, read, SourceEqualityNativeDemand.lift]
  · rw [reverseCompiled]


end MicroCFTA.SourceCurrentAllocatedNativeOrderedFinitePrefixReferenceControl
