import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistoryDefinitions
import MicroCFTA.SourceCurrentAllocatedNativeActualPrefixReturnedInduction
import MicroCFTA.SourceCurrentAllocatedNativeGeneralCNodeFinish
import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMEdgeFinish
import MicroCFTA.SourceCurrentAllocatedNativeGeneralMNodeFinish
import MicroCFTA.SourceCurrentAllocatedNativeAuthenticBodyFirstInnerHistories
import MicroCFTA.SourceCurrentAllocatedNativeAuthenticCoherentInnerHistory

/-!
# Original native C/M laws on the complete actual root history

Induction retains the public closed and original mixed memo laws.
The actual source gives the original body identity.
Each mixed finish derives its inner laws from complete empty initialization.
All laws use the fixed whole trace and original physical plans.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- Complete empty initialization establishes the original C/M laws at every actual prefix. -/
theorem current_stored_universe_general_cm_returned_at_every_actual_prefix
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel count : Nat) (rest : Control (Value Symbol Guard)) (after : Checked width)
    (bounded : count ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (actual : Trace count (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width) rest after) :
    let nodeLaw := NodeResult (width := width) rootRequest machine operations count entry body depth ordinary
    let edgeLaw := EdgeResult (width := width) rootRequest machine operations count entry body depth ordinary
    (Returned nodeLaw after.native.nodes ∧ Returned edgeLaw after.native.edges) ∧
      ∀ (used : Nat) (currentControl : Control (Value Symbol Guard)) (current : Checked width),
        used ≤ count →
        Trace used (.code (.node rootRequest .pure))
          (⟨initial width machine, operations⟩ : Checked width) currentControl current →
        Returned nodeLaw current.native.nodes ∧ Returned edgeLaw current.native.edges := by
  let nodeLaw := NodeResult (width := width) rootRequest machine operations count entry body depth ordinary
  let edgeLaw := EdgeResult (width := width) rootRequest machine operations count entry body depth ordinary
  dsimp only
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  have bodyIdentity : identity body = some bodyEntry.identity := by
    simp only [bodyShape, identity]
  apply SourceCurrentAllocatedNativeActualPrefixReturnedInduction.returned_at_every_actual_prefix
    nodeLaw edgeLaw rootRequest machine machineValid operations fuel count rest after bounded actual
  · intro finishUsed _dispatchUsed _bodyCount handle request value _beforeBody beforeFinish resume
      finishBound _total _positive finishActual _entered _running _bodyActual owner nodes edges
    constructor
    · intro closed
      exact SourceCurrentAllocatedNativeGeneralCNodeFinish.closed_result_at_actual_node_finish
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        rootRequest machine machineValid sourceGrowth operations operationsValid fuel count finishUsed handle
        request value rest after beforeFinish (resume value) bounded actual finishBound finishActual owner
        inputs fields closed ⟨nodes, edges⟩
    · intro mixed
      obtain ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,
          operandProfile, operandHeight, strictAlias, ordered⟩ := mixed
      have bodyFirstInner :=
        SourceCurrentAllocatedNativeAuthenticBodyFirstInnerHistories.body_first_inner_histories_at_authentic_prefix
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          bodyEntry.identity bodyIdentity rootRequest machine machineValid sourceGrowth operations operationsValid
          fuel count rest after bounded actual pattern patternId request.domain authentic inputs fields
          finishUsed (.code (.finishNode handle value (resume value))) beforeFinish (by omega) finishActual
      have coherentInner :=
        SourceCurrentAllocatedNativeAuthenticCoherentInnerHistory.authentic_coherent_inner_returned_at_actual_root_prefix
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          bodyEntry.identity bodyIdentity rootRequest machine machineValid sourceGrowth operations operationsValid
          fuel count finishUsed rest (.code (.finishNode handle value (resume value))) after beforeFinish
          bounded actual pattern patternId request.domain authentic (by omega) finishActual inputs fields
      exact SourceCurrentAllocatedNativeGeneralMNodeFinish.mixed_result_at_actual_node_finish
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        bodyEntry.identity bodyIdentity rootRequest machine machineValid sourceGrowth operations operationsValid
        fuel count finishUsed handle request value rest after beforeFinish (resume value)
        bounded actual finishBound finishActual owner inputs fields
        pattern patternId openAlias operand authentic aliasKind operandProfile operandHeight strictAlias ordered
        ⟨nodes, edges⟩ ⟨bodyFirstInner.1, bodyFirstInner.2, coherentInner.1, coherentInner.2⟩
  · intro finishUsed _dispatchUsed _bodyCount handle request value _beforeBody beforeFinish resume
      finishBound _total _positive finishActual _entered _running _bodyActual owner nodes edges
    exact SourceCurrentAllocatedNativeGeneralCMEdgeFinish.qualified_edge_result_at_actual_edge_finish
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      rootRequest machine machineValid sourceGrowth operations operationsValid fuel count finishUsed handle
      request value rest after beforeFinish (resume value) bounded actual finishBound finishActual owner
      inputs fields ⟨nodes, edges⟩

end MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory

#check MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
#print axioms MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
