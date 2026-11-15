import MicroCFTA.SourceCurrentAllocatedNativeCommonReaderReferenceControl
import MicroCFTA.SourceEqualityNativeDemandPrefixSplit

/-!
# Original reference control inside one actual checked execution

Both raw prefixes start at the same original control and complete state.
The actual checked whole trace supplies their physical checks and suffixes.
The final common reader is the observed completed endpoint of that trace.
No order between the entry prefix and producer prefix is assumed.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSameExecutionReferenceControl
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

/-- Same-execution prefixes derive both actual reader suffixes and source reference control. -/
theorem current_stored_universe_ref_control_in_same_execution
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
    (initial : Control Output) (start entryBefore before reader : Checked width)
    (startPhysical : Physical start.native)
    (growth : Grows sourceHeap start.native.machine.heap)
    (wholeCount entryCount producerCount : Nat) (result : Output)
    (wholeActual : Trace wholeCount initial start (.code (.pure result)) reader)
    (entryNext : Interned DomainKey → Code Symbol Guard Output)
    (entryPrefix : Steps entryCount initial start
      (.code (.enter IntersectionEmptyDomain.emptyDomain (.mu entry body depth ordinary)
        pattern entry.identity patternId entryNext)) entryBefore)
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
      (.code (.enter IntersectionEmptyDomain.emptyDomain universeValue
        pattern entry.identity patternId entryNext)) entryBefore ∧
    Trace (wholeCount - entryCount)
      (.code (.enter IntersectionEmptyDomain.emptyDomain universeValue
        pattern entry.identity patternId entryNext)) entryBefore (.code (.pure result)) reader ∧
    Trace producerCount initial start
      (.code ((compileNode ⟨entered.1,
        if referenceFirst then .reference (.interned entry.identity) else operand,
        if referenceFirst then operand else .reference (.interned entry.identity)⟩).bind next)) before ∧
    Trace (wholeCount - producerCount)
      (.code ((compileNode ⟨entered.1,
        if referenceFirst then .reference (.interned entry.identity) else operand,
        if referenceFirst then operand else .reference (.interned entry.identity)⟩).bind next))
      before (.code (.pure result)) reader ∧
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
    .code (.enter IntersectionEmptyDomain.emptyDomain universeValue
      pattern entry.identity patternId entryNext)
  let producerControl : Control Output := .code ((compileNode ⟨entered.1,
    if referenceFirst then .reference (.interned entry.identity) else operand,
    if referenceFirst then operand else .reference (.interned entry.identity)⟩).bind next)
  have entryBound := wholeActual.steps.length_le_complete entryPrefix
  have producerBound := wholeActual.steps.length_le_complete producerPrefix
  have entrySplit := checked_split_at_raw_prefix wholeActual entryPrefix entryBound
  have producerSplit := checked_split_at_raw_prefix wholeActual producerPrefix producerBound
  have entryFacts := SourceCurrentNativeEnterCommonOperand.checked_trace_extension entrySplit.1 startPhysical
  have producerFacts := SourceCurrentNativeEnterCommonOperand.checked_trace_extension producerSplit.1 startPhysical
  have beforeGrowth : Grows sourceHeap before.native.machine.heap :=
    grows_trans growth producerFacts.2.heap
  have entrySuffix : Trace (wholeCount - entryCount) entryControl entryBefore
      (.code (.pure result)) reader := entrySplit.2
  have entryPositive : 0 < wholeCount - entryCount := by
    by_contra notPositive
    have zero : wholeCount - entryCount = 0 := by omega
    have impossible : Steps 0 entryControl entryBefore (.code (.pure result)) reader := by
      simpa only [zero] using entrySuffix.steps
    have same := (steps_zero _ _ _ _ impossible).1
    cases same
  have entryLength : wholeCount - entryCount = (wholeCount - entryCount - 1) + 1 := by omega
  have enteredActual : Trace ((wholeCount - entryCount - 1) + 1) entryControl entryBefore
      (.code (.pure result)) reader := by
    exact entryLength ▸ entrySuffix
  have producerSuffix : Trace (wholeCount - producerCount) producerControl before
      (.code (.pure result)) reader := producerSplit.2
  have controlled :=
    SourceCurrentAllocatedNativeCommonReaderReferenceControl.current_stored_universe_ref_control_at_common_reader
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      pattern patternClosed patternId patternIdentity patternKind before entryBefore reader
      producerFacts.1 entryFacts.1 beforeGrowth (wholeCount - entryCount - 1)
      (wholeCount - producerCount) entryNext (.code (.pure result)) enteredActual
      operand operandAvailable operandClosed smaller referenceFirst next producerSuffix
  dsimp only
  exact ⟨entryBound, producerBound, entrySplit.1, entrySplit.2, producerSplit.1, producerSplit.2, controlled⟩

end MicroCFTA.SourceCurrentAllocatedNativeSameExecutionReferenceControl

#check MicroCFTA.SourceCurrentAllocatedNativeSameExecutionReferenceControl.current_stored_universe_ref_control_in_same_execution
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSameExecutionReferenceControl.current_stored_universe_ref_control_in_same_execution
