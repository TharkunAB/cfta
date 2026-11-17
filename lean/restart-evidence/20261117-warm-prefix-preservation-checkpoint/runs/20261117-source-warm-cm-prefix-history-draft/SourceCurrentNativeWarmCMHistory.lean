import MicroCFTA.SourceCurrentNativeWarmNodeInitialProfile
import MicroCFTA.SourceCurrentNativeWarmEdgeInitialProfile
import MicroCFTA.SourceCurrentNativeWarmCNodeFinish
import MicroCFTA.SourceCurrentNativeWarmMixedFinish
import MicroCFTA.SourceCurrentNativeWarmEdgeFinish
import MicroCFTA.SourceCurrentAllocatedNativeActualPrefixReturnedInduction
import MicroCFTA.SourceEqualityNativeDemandContinuation

namespace MicroCFTA.SourceCurrentNativeWarmCMHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity)
open SourceEqualityNativeDemand
open SourceCurrentNativeWarmCMDefinitions (NodeResult EdgeResult)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Source-derived meanings on one full warm history]
The old cold trace establishes both initial C/M laws for the fixed new
history. Its actual physical input plan also supplies both root operands.
The actual warm-prefix induction keeps that full history in every result
predicate. Concrete source finish proofs close all node and edge cases.
The mixed proof derives its four auxiliary laws internally at the same
before-finish prefix. No semantic callback is a public premise here.
-/

theorem current_stored_universe_warm_cm_returned_at_every_actual_prefix
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
    (newRoot : NodeRequest Symbol Guard) (newFuel newCount : Nat)
    (newControl : Control (Value Symbol Guard)) (warmReader : Checked width)
    (newBound : newCount ≤ newFuel)
    (newInputs : InputsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (newFields : FieldsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (newActual : Trace newCount (.code (.node newRoot .pure))
      oldSnapshot newControl warmReader) :
    let nodeLaw := NodeResult (width := width) newRoot oldSnapshot newCount entry body depth ordinary
    let edgeLaw := EdgeResult (width := width) newRoot oldSnapshot newCount entry body depth ordinary
    (Returned nodeLaw warmReader.native.nodes ∧ Returned edgeLaw warmReader.native.edges) ∧
      ∀ (used : Nat) (currentControl : Control (Value Symbol Guard)) (current : Checked width),
        used ≤ newCount →
        Trace used (.code (.node newRoot .pure)) oldSnapshot currentControl current →
        Returned nodeLaw current.native.nodes ∧ Returned edgeLaw current.native.edges
 := by
  let coldInitial : Checked width := ⟨initial width machine, operations⟩
  let nodeLaw := NodeResult (width := width) newRoot oldSnapshot newCount entry body depth ordinary
  let edgeLaw := EdgeResult (width := width) newRoot oldSnapshot newCount entry body depth ordinary
  dsimp only
  have coldPhysical : Physical (initial width machine) :=
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
  have initialNodes : Returned nodeLaw oldSnapshot.native.nodes := by
    exact SourceCurrentNativeWarmNodeInitialProfile.cold_prefix_nodes_qualified_for_actual_warm_history
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth operations operationsValid
      oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
      newRoot newFuel newCount newControl warmReader newBound newActual
  have initialEdges : Returned edgeLaw oldSnapshot.native.edges := by
    exact SourceCurrentNativeWarmEdgeInitialProfile.cold_prefix_edges_qualified_for_actual_warm_history
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
      oldLeftAvailable oldRightAvailable operations operationsValid
      oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
      newRoot newFuel newCount newControl warmReader newBound newActual
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  have bodyIdentity : identity body = some bodyEntry.identity := by
    simp only [bodyShape, identity]
  apply SourceCurrentAllocatedNativeActualPrefixReturnedInduction.returned_at_every_actual_warm_prefix
    nodeLaw edgeLaw newRoot oldSnapshot oldOperations.2.1.shape initialNodes initialEdges
    newFuel newCount newControl warmReader newBound newActual
  · intro finishUsed _dispatchUsed _bodyCount handle request value _beforeBody beforeFinish resume
      finishBound _total _positive actual _entered _running _bodyActual owner nodes edges
    constructor
    · intro closed
      exact SourceCurrentNativeWarmCNodeFinish.closed_result_at_actual_warm_node_finish
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        newRoot oldSnapshot oldOperations.2.1 oldOperations.2.2.2.1 oldOperations.2.2.2.2.1
        newFuel newCount finishUsed handle request value newControl warmReader beforeFinish (resume value)
        newBound newActual finishBound actual owner newInputs newFields closed ⟨nodes, edges⟩
    · intro mixed
      obtain ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,
        operandProfile, operandHeight, strictAlias, ordered⟩ := mixed
      exact SourceCurrentNativeWarmMixedFinish.mixed_result_at_actual_warm_node_finish
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        bodyEntry.identity bodyIdentity oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth
        operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
        newRoot newFuel newCount newControl warmReader newBound newInputs newFields newActual
        finishUsed handle request value (resume value) beforeFinish finishBound actual owner
        pattern patternId openAlias operand authentic aliasKind operandProfile operandHeight strictAlias ordered
        ⟨nodes, edges⟩
  · intro finishUsed _dispatchUsed _bodyCount handle request row _beforeBody beforeFinish resume
      finishBound _total _positive actual _entered _running _bodyActual owner nodes edges
    exact SourceCurrentNativeWarmEdgeFinish.qualified_edge_result_at_actual_warm_edge_finish
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      newRoot oldSnapshot oldOperations.2.1 oldOperations.2.2.2.1 oldOperations.2.2.2.2.1
      newFuel newCount finishUsed handle request row newControl warmReader beforeFinish (resume row)
      newBound newActual finishBound actual owner newInputs newFields ⟨nodes, edges⟩

end MicroCFTA.SourceCurrentNativeWarmCMHistory
