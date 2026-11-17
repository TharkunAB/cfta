import MicroCFTA.SourceSynthesisCurrentUniverseWarmMuAdmission
import MicroCFTA.SourceCurrentNativeWarmCMHistory
import MicroCFTA.SourceCurrentNativeAuxiliaryBaseKeyRecovery

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity tag pair)
open SourceRecursiveIntersectionDomain (extend)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Third-history node seeds from the true producer]
The middle trace separates inherited and newly returned cells once.
Each true producer supplies its actual source call admission and Gamma.
The Qualified branch gives a Profile independently of the third history.
The auxiliary branch cannot use an original singleton base domain.
The full third history remains fixed in the target mixed qualifier.
No future result law or model is a public premise.
-/
private theorem authentic_key_and_parent_apart
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
    (wholeCount : Nat) (entry : Interned NodeKey) (body depth ordinary : Node)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (pattern : Node) (patternId : Nat) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain)
 :
    domain.key = extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) ∧
      pair entry.identity patternId ≠ pair bodyEntry.identity entry.identity ∧
      pair entry.identity patternId ≠ pair entry.identity entry.identity := by
  obtain ⟨closed, identified, kind, universeFirst, used, before, next, data⟩ := authentic
  dsimp only at data
  obtain ⟨_within, entryPrefix, _ordered, one, domainSame⟩ := data
  let universeValue : Node := .mu entry body depth ordinary
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
  refine ⟨?_, apart⟩
  rw [domainSame]
  exact keyShape

private theorem auxiliary_domain_cannot_be_authentic_base
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
    (wholeCount : Nat) (entry : Interned NodeKey) (body depth ordinary : Node)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (pattern : Node) (patternId : Nat) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain)
    (requestDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (auxiliary :
      requestDomain.key = extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity) ∨
      requestDomain.key = extend (extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity))
        [entry.identity] (pair entry.identity entry.identity) ∨
      requestDomain.key = extend domain.key [entry.identity] (pair entry.identity entry.identity) ∨
      requestDomain.key = extend (extend domain.key [entry.identity] (pair entry.identity entry.identity))
        [entry.identity] (pair bodyEntry.identity entry.identity))
    (targetRoot : NodeRequest Symbol Guard) (targetStart : Checked width)
    (targetPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid targetStart.native)
    (targetCount : Nat) (targetPattern : Node) (targetPatternId : Nat)
    (targetAuthentic : AuthenticEntryAt (width := width) targetRoot targetStart targetCount
      entry body depth ordinary targetPattern targetPatternId requestDomain) : False := by
  have old := authentic_key_and_parent_apart (width := width) rootRequest start initialPhysical
    wholeCount entry body depth ordinary bodyEntry bodyRows bodyShape pattern patternId domain authentic
  have target := authentic_key_and_parent_apart (width := width) targetRoot targetStart targetPhysical
    targetCount entry body depth ordinary bodyEntry bodyRows bodyShape targetPattern targetPatternId
    requestDomain targetAuthentic
  have oldShape :
      requestDomain.key = extend (extend IntersectionEmptyDomain.emptyKey [entry.identity]
        (pair entry.identity patternId)) [entry.identity] (pair bodyEntry.identity entry.identity) ∨
      requestDomain.key = extend (extend (extend IntersectionEmptyDomain.emptyKey [entry.identity]
        (pair entry.identity patternId)) [entry.identity] (pair bodyEntry.identity entry.identity))
        [entry.identity] (pair entry.identity entry.identity) ∨
      requestDomain.key = extend (extend IntersectionEmptyDomain.emptyKey [entry.identity]
        (pair entry.identity patternId)) [entry.identity] (pair entry.identity entry.identity) ∨
      requestDomain.key = extend (extend (extend IntersectionEmptyDomain.emptyKey [entry.identity]
        (pair entry.identity patternId)) [entry.identity] (pair entry.identity entry.identity))
        [entry.identity] (pair bodyEntry.identity entry.identity) := by
    simpa only [old.1] using auxiliary
  have different := SourceCurrentNativeAuxiliaryBaseKeyRecovery.auxiliary_key_ne_singleton_base
    entry.identity (pair entry.identity patternId) (pair bodyEntry.identity entry.identity)
    (pair entry.identity entry.identity) requestDomain.key (pair entry.identity targetPatternId)
    old.2.1 old.2.2 oldShape
  exact different target.1

theorem original_universe_two_prefix_node_seed_for_third_actual_history
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (oldRootDomain : oldRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (oldRootClosed : oldRoot.left.free = [] ∧ oldRoot.right.free = [])
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap machine.heap)
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
    (middleRoot : NodeRequest Symbol Guard) (middleFuel : Nat)
    (middleRootDomain : middleRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (middleLeftAvailable : Available oldSnapshot.native.machine.heap middleRoot.left)
    (middleRightAvailable : Available oldSnapshot.native.machine.heap middleRoot.right)
    (middleLeftClosed : middleRoot.left.free = []) (middleRightClosed : middleRoot.right.free = [])
    (middleInputs : InputsThrough middleFuel (.code (.node middleRoot .pure)) oldSnapshot)
    (middleFields : FieldsThrough middleFuel (.code (.node middleRoot .pure)) oldSnapshot)
    (middleCount : Nat) (middleControl : Control (Value Symbol Guard))
    (middleSnapshot : Checked width) (middleBound : middleCount ≤ middleFuel)
    (middleActual : Trace middleCount (.code (.node middleRoot .pure))
      oldSnapshot middleControl middleSnapshot)
    (nextRoot : NodeRequest Symbol Guard) (nextFuel nextCount : Nat)
    (nextControl : Control (Value Symbol Guard)) (reader : Checked width)
    (nextRootDomain : nextRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (nextRootAvailable : Available middleSnapshot.native.machine.heap nextRoot.left ∧
      Available middleSnapshot.native.machine.heap nextRoot.right)
    (nextRootClosed : nextRoot.left.free = [] ∧ nextRoot.right.free = [])
    (nextBound : nextCount ≤ nextFuel)
    (nextInputs : InputsThrough nextFuel (.code (.node nextRoot .pure)) middleSnapshot)
    (nextFields : FieldsThrough nextFuel (.code (.node nextRoot .pure)) middleSnapshot)
    (nextActual : Trace nextCount (.code (.node nextRoot .pure)) middleSnapshot
      nextControl reader) :
    Returned (SourceCurrentNativeWarmCMDefinitions.NodeResult (width := width)
      nextRoot middleSnapshot nextCount entry body depth ordinary) middleSnapshot.native.nodes := by
  have _retainedThirdAdmissions := And.intro nextRootDomain
    (And.intro nextRootAvailable (And.intro nextRootClosed
      (And.intro nextBound (And.intro nextInputs (And.intro nextFields nextActual)))))
  let coldInitial : Checked width := ⟨initial width machine, operations⟩
  have coldPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have oldCurrent : Inputs (.code (.node oldRoot .pure)) coldInitial := by
    cases oldFuel with
    | zero => exact oldInputs
    | succ remaining => exact oldInputs.1
  have oldLeftAvailable : Available machine.heap oldRoot.left := oldCurrent.1.2.1
  have oldRightAvailable : Available machine.heap oldRoot.right := oldCurrent.1.2.2
  have oldOperations := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    oldFuel oldCount (.code (.node oldRoot .pure)) oldControl .pure coldInitial oldSnapshot sourceHeap
    coldPhysical oldInputs oldFields operationsValid sourceGrowth
    (by simpa only [Control.bind_pure] using oldActual.steps) oldBound
  have middlePhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension middleActual oldOperations.2.1).1
  have leftProfile : Profile entry.identity oldRoot.left :=
    ⟨oldRootClosed.1,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        machine.heap machineValid.1.coherent pastInventory oldRoot.left oldLeftAvailable oldRootClosed.1⟩
  have rightProfile : Profile entry.identity oldRoot.right :=
    ⟨oldRootClosed.2,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        machine.heap machineValid.1.coherent pastInventory oldRoot.right oldRightAvailable oldRootClosed.2⟩
  have coldInventory := original_universe_cold_query_no_new_mu
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine machineValid sourceGrowth oldRootDomain leftProfile rightProfile
    operations operationsValid oldFuel oldInputs oldFields
  have inventoryAtOld : InternedShallowHeap.NoNewMu sourceHeap oldSnapshot.native.machine.heap :=
    InternedShallowHeap.noNewMu_trans pastInventory
      (coldInventory.2 oldCount oldControl oldSnapshot oldBound oldActual)
  have oldGamma :=
    SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine machineValid sourceGrowth operations operationsValid oldFuel oldCount oldControl oldSnapshot
      oldBound oldInputs oldFields oldActual
  have middleGamma :=
    SourceCurrentNativeWarmCMHistory.current_stored_universe_warm_cm_returned_at_every_actual_prefix
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
      operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
      middleRoot middleFuel middleCount middleControl middleSnapshot middleBound middleInputs middleFields middleActual
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  let bodyRows := canonicalEdges (_arrow :: _sourceRows)
  have bodyRead : body = .node bodyEntry bodyRows 0 [.interned entry.identity] := bodyShape
  have bodyIdentity : identity body = some bodyEntry.identity := by
    rw [bodyRead]
    rfl
  intro handle request value currentCell
  constructor
  · intro closed
    exact (middleGamma.1.1 handle request value currentCell).1 closed
  · intro mixed
    obtain ⟨targetPattern, targetPatternId, _targetAlias, _targetOperand, targetAuthentic,
      _targetAliasKind, _targetProfile, _targetHeight, _targetStrict, _targetOrder⟩ := mixed
    have excluded
        (producerRoot : NodeRequest Symbol Guard) (producerStart : Checked width)
        (producerPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid producerStart.native)
        (producerCount : Nat) (pattern : Node) (patternId : Nat)
        (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
        (authentic : AuthenticEntryAt (width := width) producerRoot producerStart producerCount
          entry body depth ordinary pattern patternId domain)
        (keys :
        request.domain.key = extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity) ∨
        request.domain.key = extend (extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity))
          [entry.identity] (pair entry.identity entry.identity) ∨
        request.domain.key = extend domain.key [entry.identity] (pair entry.identity entry.identity) ∨
        request.domain.key = extend (extend domain.key [entry.identity] (pair entry.identity entry.identity))
          [entry.identity] (pair bodyEntry.identity entry.identity)) : False := by
      exact auxiliary_domain_cannot_be_authentic_base (width := width)
        producerRoot producerStart producerPhysical producerCount entry body depth ordinary
        bodyEntry bodyRows bodyRead pattern patternId domain authentic request.domain keys
        nextRoot middleSnapshot middlePhysical nextCount targetPattern targetPatternId targetAuthentic
    rcases SourceCurrentAllocatedNativeNodeReturnOrigin.returned_node_cell_or_finish_prefix
        middleActual handle request value currentCell with inherited | produced
    · obtain ⟨_finishUsed, _suffixCount, _beforeFinish, _continuation, _queryUsed, _bodyCount,
        _queryBefore, _beforeBody, _queryNext, _finishTotal, _finishSmall, _finishFuel,
        _finishActual, _owner, _finishEvent, _finished, _suffix, _queryTotal, _querySmall,
        _queryFuel, _queryActual, _dispatch, _isolated, _physical, _ready, _safe,
        _bodyOwner, _bodyActual, _nextSame, bodyId, bodyIdRead, admitted⟩ :=
      original_universe_returned_node_full_admission (width := width)
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        oldRoot machine machineValid sourceGrowth pastInventory oldRootDomain oldLeftAvailable oldRightAvailable
        oldRootClosed.1 oldRootClosed.2 operations oldFuel oldCount oldControl oldSnapshot oldBound oldActual
        handle request value inherited
      rcases admitted with qualified | auxiliary
      · rcases qualified with closed | oldMixed
        · exact (oldGamma.1.1 handle request value inherited).1 closed
        · exact (oldGamma.1.1 handle request value inherited).2 oldMixed
      · have bodyIdSame : bodyId = bodyEntry.identity := Option.some.inj (bodyIdRead.symm.trans bodyIdentity)
        subst bodyId
        obtain ⟨pattern, patternId, domain, authentic, alternatives⟩ := auxiliary
        dsimp only at alternatives
        have keys :
          request.domain.key = extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity) ∨
          request.domain.key = extend (extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity))
            [entry.identity] (pair entry.identity entry.identity) ∨
          request.domain.key = extend domain.key [entry.identity] (pair entry.identity entry.identity) ∨
          request.domain.key = extend (extend domain.key [entry.identity] (pair entry.identity entry.identity))
            [entry.identity] (pair bodyEntry.identity entry.identity) := by
          rcases alternatives with ⟨same, _⟩ | ⟨same, _, _⟩ | ⟨same, _⟩ | ⟨same, _⟩
          · exact Or.inl same
          · exact Or.inr (Or.inl same)
          · exact Or.inr (Or.inr (Or.inl same))
          · exact Or.inr (Or.inr (Or.inr same))
        exact (excluded oldRoot coldInitial coldPhysical oldCount pattern patternId domain authentic keys).elim
    · obtain ⟨finishUsed, _suffixCount, beforeFinish, continuation, total,
        finishActual, owner, _finishEvent, _finished, _suffix⟩ := produced
      obtain ⟨queryUsed, _bodyCount, queryBefore, _beforeBody, queryNext, queryTotal,
          _querySmall, _queryFuel, queryActual, _dispatch, _isolated, _queryPhysical,
          _ready, _safe, _bodyOwner, _bodyActual, _nextSame⟩ :=
        SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
          middleRoot oldSnapshot oldOperations.2.1 middleFuel finishUsed handle request value continuation
          beforeFinish (by omega) finishActual owner
      obtain ⟨bodyId, bodyIdRead, admitted⟩ := original_universe_warm_node_query_prefix_full_admission
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        middleRoot oldSnapshot oldOperations.2.1 oldOperations.2.2.2.1 inventoryAtOld
        middleRootDomain middleLeftAvailable middleRightAvailable middleLeftClosed middleRightClosed
        middleFuel middleCount queryUsed middleBound middleInputs middleFields
        request queryNext queryBefore (by omega) queryActual
      rcases admitted with qualified | auxiliary
      · rcases qualified with closed | oldMixed
        · exact (middleGamma.1.1 handle request value currentCell).1 closed
        · exact (middleGamma.1.1 handle request value currentCell).2 oldMixed
      · have bodyIdSame : bodyId = bodyEntry.identity := Option.some.inj (bodyIdRead.symm.trans bodyIdentity)
        subst bodyId
        obtain ⟨pattern, patternId, domain, authentic, alternatives⟩ := auxiliary
        dsimp only at alternatives
        have keys :
          request.domain.key = extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity) ∨
          request.domain.key = extend (extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity))
            [entry.identity] (pair entry.identity entry.identity) ∨
          request.domain.key = extend domain.key [entry.identity] (pair entry.identity entry.identity) ∨
          request.domain.key = extend (extend domain.key [entry.identity] (pair entry.identity entry.identity))
            [entry.identity] (pair bodyEntry.identity entry.identity) := by
          rcases alternatives with ⟨same, _⟩ | ⟨same, _, _⟩ | ⟨same, _⟩ | ⟨same, _⟩
          · exact Or.inl same
          · exact Or.inr (Or.inl same)
          · exact Or.inr (Or.inr (Or.inl same))
          · exact Or.inr (Or.inr (Or.inr same))
        exact (excluded middleRoot oldSnapshot oldOperations.2.1 middleCount
          pattern patternId domain authentic keys).elim

end MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
