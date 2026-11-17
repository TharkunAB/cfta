import MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload

namespace MicroCFTA.SourceCurrentNativeWarmNodeInitialProfile
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Initial meanings for the same full warm history]
The old cold trace supplies the initial returned cells. The new full trace
fixes every later mixed qualifier. A qualifier can use an entry after an
earlier read. Keep its full count when selecting that actual entry.
The result is the node seed required by the existing query induction.
It is derived from source history. No initial semantic law is a premise.
-/

theorem cold_prefix_nodes_qualified_for_actual_warm_history
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
    (newActual : Trace newCount (.code (.node newRoot .pure))
      oldSnapshot newControl warmReader) :
    Returned (fun request value =>
      (SourceCurrentAllocatedNativeGeneralCMHistory.ClosedQualified entry.identity request →
        SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity value) ∧
      (SourceCurrentAllocatedNativeSourceWarmEntry.MixedQualifiedAt (width := width)
          newRoot oldSnapshot newCount entry body depth ordinary request →
        SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity value))
      oldSnapshot.native.nodes := by
  have oldGamma :=
    SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine machineValid sourceGrowth operations operationsValid oldFuel oldCount oldControl oldSnapshot
      oldBound oldInputs oldFields oldActual
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  have universeClosed : (Value.mu entry body depth ordinary).free = [] := by
    rw [bodyShape]
    simp [Value.free]
  intro handle request value oldCell
  constructor
  · intro closed
    exact (oldGamma.1.1 handle request value oldCell).1 closed
  · intro mixed
    obtain ⟨pattern, patternId, openAlias, operand, authentic,
      aliasKind, operandProfile, operandHeight, strictAlias, ordered⟩ := mixed
    obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst,
      entryUsed, beforeEntry, next, entryData⟩ := authentic
    dsimp only at entryData
    obtain ⟨entryBound, entryPrefix, _allocation, oneEntry, domainEq⟩ := entryData
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter beforeEntry.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    let entering : Control (Value Symbol Guard) :=
      .code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then universeValue else pattern)
        (if universeFirst then pattern else universeValue)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) next)
    let nextMachine : Machine Symbol Guard :=
      {beforeEntry.native.machine with domains := entered.2}
    let started : Checked width := {beforeEntry with native := advance beforeEntry.native nextMachine}
    have actualPrefix : Trace entryUsed (.code (.node newRoot .pure)) oldSnapshot entering beforeEntry :=
      entryPrefix
    have actualEntry : Trace 1 entering beforeEntry (.code (next entered.1)) started :=
      oneEntry
    have total : entryUsed + (newCount - entryUsed) = newCount := by omega
    have wholeTrace : Trace (entryUsed + (newCount - entryUsed))
        (.code (.node newRoot .pure)) oldSnapshot newControl warmReader := by
      simpa only [total] using newActual
    have prefixSplit := SourceCurrentHereditaryNativePhysicalSplit.split actualPrefix.steps wholeTrace
    have remaining : 1 + (newCount - entryUsed - 1) = newCount - entryUsed := by omega
    have fromEntry : Trace (1 + (newCount - entryUsed - 1))
        entering beforeEntry newControl warmReader := by
      simpa only [remaining] using prefixSplit.2
    have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split actualEntry.steps fromEntry
    have actualDomain : request.domain = entered.1 := domainEq
    have matchingKey : request.domain.key = entered.1.key :=
      congrArg (fun domain : Interned IntersectionFlatMemoKeyDomain.DomainKey => domain.key) actualDomain
    have result :=
      SourceCurrentAllocatedNativePastGammaEqualEntryPayload.closed_root_cold_returned_mixed_profile_after_later_entry
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        oldRoot machine oldRootDomain oldRootClosed universeClosed
        machineValid sourceGrowth operations operationsValid oldFuel oldCount oldControl
        oldSnapshot oldBound oldActual oldInputs oldFields handle request value oldCell
        pattern patternClosed patternId patternIdentity patternKind universeFirst next newRoot newFuel entryUsed
        beforeEntry started (.code (next entered.1)) (by omega) prefixSplit.1 entrySplit.1 matchingKey
        openAlias operand aliasKind operandProfile operandHeight strictAlias ordered
    exact result.2.1

end MicroCFTA.SourceCurrentNativeWarmNodeInitialProfile

#check @MicroCFTA.SourceCurrentNativeWarmNodeInitialProfile.cold_prefix_nodes_qualified_for_actual_warm_history
#print axioms MicroCFTA.SourceCurrentNativeWarmNodeInitialProfile.cold_prefix_nodes_qualified_for_actual_warm_history
