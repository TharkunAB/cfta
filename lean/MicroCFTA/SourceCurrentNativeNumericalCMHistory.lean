import MicroCFTA.SourceCurrentNativeNumericalSeedInvariant
import MicroCFTA.SourceCurrentNativeNumericalBodyFirstCallbacks
import MicroCFTA.SourceCurrentNativeNumericalCoherentCallbacks
import MicroCFTA.SourceCurrentNativeWarmCNodeFinish
import MicroCFTA.SourceCurrentNativeWarmMixedFinish
import MicroCFTA.SourceCurrentNativeWarmEdgeFinish
import MicroCFTA.SourceCurrentAllocatedNativeActualPrefixReturnedInduction
import MicroCFTA.SourceEqualityNativeDemandContinuation

namespace MicroCFTA.SourceCurrentNativeNumericalCMHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeNumericalSeedInvariant (Seeds)
open SourceCurrentNativeWarmCMDefinitions (NodeResult EdgeResult)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [One retained query with numerical past seeds]
The four auxiliary families preserve genuine past laws at every actual prefix.
Their numerical source callbacks need no future pattern at query start.
One fixed full history qualifies the main C/M induction throughout.
Concrete finish proofs consume the same before-finish main and inner laws.
Past Seeds is an internal smaller-query hypothesis, not a final source supplier.
-/

private theorem authentic_numerical_key_and_identity_apart
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (wholeCount : Nat) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (pattern : Value Symbol Guard) (patternId : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain) :
    domain.key = extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) ∧
      patternId ≠ entry.identity ∧ patternId ≠ bodyEntry.identity := by
  obtain ⟨closed, identified, kind, universeFirst, used, before, next, data⟩ := authentic
  dsimp only at data
  obtain ⟨_within, entryPrefix, _ordered, one, domainSame⟩ := data
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let after : Checked width :=
    {before with native := advance before.native {before.native.machine with domains := entered.2}}
  change domain = entered.1 at domainSame
  have beforePhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension entryPrefix initialPhysical).1
  have receipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary pattern closed patternId identified kind universeFirst
    next 0 before after (.code (next entered.1)) beforePhysical one
  obtain ⟨_allocation, _step, _event, _tail, _heap, _domains, _operations,
    universeAvailable, patternAvailable, _universeAfter, _patternAfter, _startedDomain,
    _readerDomain, keyShape, _nonempty, _afterPhysical, _extension, _classify⟩ := receipt
  have shapedUniverse : Available before.native.machine.heap
      (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    rw [← bodyShape]
    exact universeAvailable
  have apart := SourceCurrentNativeAuxiliaryBaseKeyRecovery.source_parent_pair_avoids_auxiliary
    before.native.machine.heap beforePhysical.machine.1 entry bodyEntry bodyRows depth ordinary
    shapedUniverse pattern patternId patternAvailable closed identified kind
  have numbers : patternId ≠ entry.identity ∧ patternId ≠ bodyEntry.identity := by
    constructor
    · intro same
      exact apart.2 (congrArg (pair entry.identity) same)
    · intro same
      apply apart.1
      rw [same]
      exact Prod.ext (Nat.min_comm _ _) (Nat.max_comm _ _)
  refine ⟨?_, numbers⟩
  rw [domainSame]
  exact keyShape

private theorem numerical_auxiliary_payloads_at_actual_prefix
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel prefixCount : Nat) (prefixControl : Control (Value Symbol Guard)) (current : Checked width)
    (prefixBound : prefixCount ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) start)
    (prefixActual : Trace prefixCount (.code (.node rootRequest .pure)) start prefixControl current)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId start) :
    ∀ patternId : Nat, patternId ≠ entry.identity → patternId ≠ bodyId →
      let domain : IntersectionFlatMemoKeyDomain.DomainKey :=
        extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId)
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let bodyFirst := extend domain [entry.identity] (pair bodyId entry.identity)
      let diagonalFirst := extend domain [entry.identity] (pair entry.identity entry.identity)
      let diagonalTerminal := extend diagonalFirst [entry.identity] (pair bodyId entry.identity)
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId bodyFirst body universeValue) current.native.nodes ∧
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
        entry.identity bodyId bodyFirst universeValue) current.native.edges ∧
      Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue)
        current.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult current.native.edges := by
  intro patternId universeApart bodyApart
  dsimp only [Seeds] at pastSeeds
  obtain ⟨_inventory, _closedNodes, _closedEdges, _singletonNodes, _singletonEdges, auxiliary⟩ := pastSeeds
  have initial := auxiliary patternId universeApart bodyApart
  let baseKey := extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId)
  let bodyFirst := extend baseKey [entry.identity] (pair bodyId entry.identity)
  let diagonalFirst := extend baseKey [entry.identity] (pair entry.identity entry.identity)
  let diagonalTerminal := extend diagonalFirst [entry.identity] (pair bodyId entry.identity)
  obtain ⟨bodyCompiler, selected, childPure, absent, bodyRead⟩ :=
    SourceCurrentNativeNumericalBodyFirstCallbacks.original_universe_body_first_callbacks_at_numerical_base
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity start.native.machine.heap initialPhysical.machine.1 sourceGrowth
      patternId universeApart bodyApart
  obtain ⟨coherentCompiler, orderedInputs, rightMu, childKey, pairedApart, coherentRead⟩ :=
    SourceCurrentNativeNumericalCoherentCallbacks.original_universe_coherent_callbacks_at_numerical_base
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity start.native.machine.heap initialPhysical.machine.1 sourceGrowth
      patternId universeApart bodyApart
  have prefixInputs := SourceCurrentAllocatedNativeSourceQueryInduction.through_mono
    fuel prefixCount (.code (.node rootRequest .pure)) start prefixBound inputs
  have prefixFields := SourceCurrentAllocatedNativeSourceQueryInduction.fields_mono
    fuel prefixCount (.code (.node rootRequest .pure)) start prefixBound fields
  have bodyEngine := SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.query_returned_and_raw_results
    (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyFirst bodyId bodyCompiler selected childPure absent bodyRead prefixCount
  have bodyReturned := (bodyEngine.1 rootRequest start initialPhysical sourceGrowth operationsValid
    prefixInputs prefixFields initial.1 initial.2.1).1
  have coherentEngine := SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.query_returned_and_raw_results
    (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    diagonalTerminal entry.identity entry.identity coherentCompiler orderedInputs diagonalFirst bodyId
    rightMu bodyIdentity childKey pairedApart coherentRead prefixCount
  have coherentReturned := (coherentEngine.1 rootRequest start initialPhysical sourceGrowth operationsValid
    prefixInputs prefixFields initial.2.2.1 initial.2.2.2).1
  have exactExecution := SourceEqualityNativeDemand.Steps.execute prefixCount
    (.code (.node rootRequest .pure)) prefixControl start current prefixActual.steps
  rw [exactExecution] at bodyReturned coherentReturned
  exact ⟨bodyReturned.1, bodyReturned.2, coherentReturned.1, coherentReturned.2⟩

theorem auxiliary_payloads_at_actual_prefix_of_past_seeds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount : Nat) (rest : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) start)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure)) start rest reader)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId start)
    (prefixCount : Nat) (prefixControl : Control (Value Symbol Guard)) (current : Checked width)
    (prefixBound : prefixCount ≤ wholeCount)
    (prefixActual : Trace prefixCount (.code (.node rootRequest .pure)) start prefixControl current)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain) :
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
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult current.native.edges := by
  have _retainedWholeTrace := wholeActual
  obtain ⟨bodyEntry, _marker, arrow, rows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  have actualBodyIdentity : identity body = some bodyEntry.identity := by
    rw [bodyShape]
    rfl
  have bodyIdEq : bodyEntry.identity = bodyId :=
    Option.some.inj (actualBodyIdentity.symm.trans bodyIdentity)
  have entryFacts := authentic_numerical_key_and_identity_apart rootRequest start initialPhysical
    wholeCount entry body depth ordinary bodyEntry (canonicalEdges (arrow :: rows)) bodyShape
    pattern patternId domain authentic
  have numeric := numerical_auxiliary_payloads_at_actual_prefix
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity rootRequest start initialPhysical sourceGrowth operationsValid
    fuel prefixCount prefixControl current (by omega) inputs fields prefixActual pastSeeds
  have chosen := numeric patternId entryFacts.2.1
    (fun same => entryFacts.2.2 (same.trans bodyIdEq.symm))
  simpa only [entryFacts.1] using chosen

theorem returned_at_every_actual_prefix_of_past_seeds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount : Nat) (rest : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) start)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure)) start rest reader)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId start) :
    let nodeLaw := NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary
    let edgeLaw := EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary
    (Returned nodeLaw reader.native.nodes ∧ Returned edgeLaw reader.native.edges) ∧
      ∀ (used : Nat) (currentControl : Control (Value Symbol Guard)) (current : Checked width),
        used ≤ wholeCount →
        Trace used (.code (.node rootRequest .pure)) start currentControl current →
        Returned nodeLaw current.native.nodes ∧ Returned edgeLaw current.native.edges := by
  let nodeLaw := NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary
  let edgeLaw := EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary
  dsimp only
  have initial := SourceCurrentNativeNumericalSeedInvariant.initial_payloads_for_actual_history_of_past_seeds
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity rootRequest start initialPhysical sourceGrowth operationsValid
    fuel wholeCount rest reader wholeBound inputs fields wholeActual pastSeeds
  apply SourceCurrentAllocatedNativeActualPrefixReturnedInduction.returned_at_every_actual_warm_prefix
    nodeLaw edgeLaw rootRequest start initialPhysical.shape initial.1.1 initial.1.2
    fuel wholeCount rest reader wholeBound wholeActual
  · intro finishUsed _dispatchUsed _bodyCount handle request value _beforeBody beforeFinish resume
      finishBound _total _positive actual _entered _running _bodyActual owner nodes edges
    constructor
    · intro closed
      exact SourceCurrentNativeWarmCNodeFinish.closed_result_at_actual_warm_node_finish
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        rootRequest start initialPhysical sourceGrowth operationsValid
        fuel wholeCount finishUsed handle request value rest reader beforeFinish (resume value)
        wholeBound wholeActual finishBound actual owner inputs fields closed ⟨nodes, edges⟩
    · intro mixed
      obtain ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,
        operandProfile, operandHeight, strictAlias, ordered⟩ := mixed
      have innerPast := auxiliary_payloads_at_actual_prefix_of_past_seeds
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        bodyId bodyIdentity rootRequest start initialPhysical sourceGrowth operationsValid
        fuel wholeCount rest reader wholeBound inputs fields wholeActual pastSeeds
        finishUsed (.code (.finishNode handle value (resume value))) beforeFinish (by omega) actual
        pattern patternId request.domain authentic
      exact SourceCurrentNativeWarmMixedFinish.mixed_result_at_actual_warm_node_finish_of_past_inner_laws
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        bodyId bodyIdentity rootRequest start initialPhysical sourceGrowth operationsValid
        fuel wholeCount finishUsed handle request value rest reader beforeFinish (resume value)
        wholeBound wholeActual finishBound actual owner inputs fields
        pattern patternId openAlias operand authentic aliasKind operandProfile operandHeight strictAlias ordered
        ⟨nodes, edges⟩ innerPast
  · intro finishUsed _dispatchUsed _bodyCount handle request row _beforeBody beforeFinish resume
      finishBound _total _positive actual _entered _running _bodyActual owner nodes edges
    exact SourceCurrentNativeWarmEdgeFinish.qualified_edge_result_at_actual_warm_edge_finish
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      rootRequest start initialPhysical sourceGrowth operationsValid
      fuel wholeCount finishUsed handle request row rest reader beforeFinish (resume row)
      wholeBound wholeActual finishBound actual owner inputs fields ⟨nodes, edges⟩

end MicroCFTA.SourceCurrentNativeNumericalCMHistory

namespace MicroCFTA.SourceCurrentNativeNumericalCMHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeNumericalSeedInvariant (Seeds)
open SourceCurrentNativeWarmCMDefinitions (NodeResult EdgeResult)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false


/- Note [Pointwise auxiliary laws for the query invariant]
Seeds quantifies over every numerical pattern identity with the source exclusions.
The preserved family laws do not require an executed future entry.
This export exposes the existing actual-prefix proof for the next induction step.
Past Seeds remains an internal smaller-query hypothesis.
-/

theorem numerical_auxiliary_payloads_at_actual_prefix_of_past_seeds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel prefixCount : Nat) (prefixControl : Control (Value Symbol Guard)) (current : Checked width)
    (prefixBound : prefixCount ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) start)
    (prefixActual : Trace prefixCount (.code (.node rootRequest .pure)) start prefixControl current)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId start) :
    ∀ patternId : Nat, patternId ≠ entry.identity → patternId ≠ bodyId →
      let domain : IntersectionFlatMemoKeyDomain.DomainKey :=
        extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId)
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let bodyFirst := extend domain [entry.identity] (pair bodyId entry.identity)
      let diagonalFirst := extend domain [entry.identity] (pair entry.identity entry.identity)
      let diagonalTerminal := extend diagonalFirst [entry.identity] (pair bodyId entry.identity)
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId bodyFirst body universeValue) current.native.nodes ∧
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
        entry.identity bodyId bodyFirst universeValue) current.native.edges ∧
      Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue)
        current.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult current.native.edges := by
  exact numerical_auxiliary_payloads_at_actual_prefix (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity rootRequest start initialPhysical sourceGrowth operationsValid
    fuel prefixCount prefixControl current prefixBound inputs fields prefixActual pastSeeds

end MicroCFTA.SourceCurrentNativeNumericalCMHistory
