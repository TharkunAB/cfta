-- UNCOMPILED CANDIDATE. No proof credit.
import MicroCFTA.SourceCurrentAllocatedNativeMixedReferenceControl
import MicroCFTA.SourceCurrentNativeEnterCommonOperand

/-!
# Reference control at one observed common reader

Two actual checked suffixes end at the same complete reader state.
The entry suffix supplies the full pattern at that reader.
The producer suffix retains the actual current operand there.
Past source growth supplies the original complete U at the producer.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCommonReaderReferenceControl
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisUniversePrefixHeight (height)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand (Control)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeMixedReferenceControl

set_option autoImplicit false
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- Actual suffixes derive source reference lookup and both control orientations at one reader. -/
theorem current_stored_universe_ref_control_at_common_reader
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
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
    (before entryBefore reader : Checked width)
    (physical : Physical before.native) (entryPhysical : Physical entryBefore.native)
    (growth : Grows sourceHeap before.native.machine.heap)
    (entryFuel fuel : Nat) (entryNext : Interned DomainKey → Code Symbol Guard Node)
    (rest : Control Node)
    (entryActual : Trace (entryFuel + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain (.mu entry body depth ordinary)
        pattern entry.identity patternId entryNext)) entryBefore rest reader)
    (operand : Node) (operandAvailable : Available before.native.machine.heap operand)
    (operandClosed : operand.free = []) (smaller : height operand < height pattern)
    (referenceFirst : Bool)
    (actual :
      let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
        IntersectionEmptyDomain.emptyKey (.mu entry body depth ordinary) pattern entry.identity patternId
      Trace fuel (.code (compileNode ⟨entered.1,
        if referenceFirst then .reference (.interned entry.identity) else operand,
        if referenceFirst then operand else .reference (.interned entry.identity)⟩))
        before rest reader) :
    let universeValue : Node := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
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
  have receipt := SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
    IntersectionEmptyDomain.emptyDomain universeValue pattern entry.identity patternId entryNext
    entryFuel entryBefore reader rest entryPhysical entryActual
  obtain ⟨_one, _tail, _heap, _domains, _operations, _oldDomain,
    _leftBefore, _rightBefore, _leftReader, patternReader, _enteredDomain, _readerDomain,
    enteredKey, _entryGrowth, _sameRecords⟩ := receipt
  have later := SourceCurrentNativeEnterCommonOperand.checked_trace_extension actual physical
  have operandReader : Available reader.native.machine.heap operand :=
    later.2.available operand operandAvailable
  have universeAvailable : Available before.native.machine.heap universeValue :=
    physical.machine.1.cached.nodes key _ (growth.nodeRecords key _ stored)
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
    left
    simp [universeValue, SourceRecursiveIntersectionEnvironment.bindings,
      SourceRecursiveIntersectionEnvironment.binder]
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
        ((SourceRecursiveIntersectionEnvironment.bindings universeValue pattern).map Prod.fst)
        (pair entry.identity patternId) candidate).mp member with same | old
      · exact differentKey same
      · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at old
    exact ⟨absent _ directApart, absent _ reverseApart⟩
  have notRepeated := fresh_reference_decisions entered.1 entry.identity operand allFresh
  dsimp only
  refine ⟨universeClosed, universeAvailable, later.2, bound, found, read,
    notRepeated.1, notRepeated.2, ?_⟩
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

end MicroCFTA.SourceCurrentAllocatedNativeCommonReaderReferenceControl
