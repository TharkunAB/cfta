import MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
import MicroCFTA.SourcePruningEnumerationNativeBodyOriginArity
import MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit
import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourceEqualityNativeDemandWalkExecution
import MicroCFTA.MergedPhysicalGroupEdges

namespace MicroCFTA.SourceCurrentAllocatedNativeCheckedEdgeBodyProfile
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Pair" => Node × Node
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

set_option autoImplicit false

private theorem through_head
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (fuel : Nat) (control : Control Node) (state : Checked width)
    (plan : InputsThrough fuel control state) : Inputs control state := by
  cases fuel with
  | zero => exact plan
  | succ fuel => exact plan.1

private theorem empty_profile (sourceName : Nat) : Profile sourceName (.empty : Node) := by
  constructor
  · rfl
  · intro atom member
    simp only [InternedBoundaryAtoms.atoms, List.not_mem_nil] at member

private theorem profiles_of_all_two {members : List Pair} {values : List Node} (sourceName : Nat)
    (aligned : All₂ (fun _ value => Profile sourceName value) members values) :
    ∀ value ∈ values, Profile sourceName value := by
  induction aligned with
  | nil => intro value member; cases member
  | cons head tail ih =>
      intro value member
      cases member with
      | head => exact head
      | tail _ member => exact ih value member

private theorem protected_body_first
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (request : EdgeRequest Symbol Guard) (bodySteps : Nat) (before after : Checked width) (result : Row)
    (actual : Trace bodySteps (.edgeBody request .pure) before (.code (.pure result)) after) :
    ∃ (code : Code Symbol Guard Row) (started : Checked width) (rest : Nat),
      bodySteps = rest + 1 ∧
      SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) started ∧
      Trace rest (.code code) started (.code (.pure result)) after := by
  cases actual with
  | cons start state next current final reached count _inputs one tail =>
      obtain ⟨code, same⟩ := SourceEqualityNativeDemandBodyYield.pure_yielded_code
        request before current next one
      subst next
      exact ⟨code, current, count, rfl, one, tail⟩

private theorem walk_profiles
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard) (sourceName : Nat)
    (request : EdgeRequest Symbol Guard) (original : Checked width) (parentFuel bodySteps : Nat)
    (physicalOriginal : Physical original.native) (sourceGrowth : Grows sourceHeap original.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid original.operations)
    (plan : InputsThrough parentFuel (.code (.edge request .pure)) original)
    (fields : FieldsThrough parentFuel (.code (.edge request .pure)) original)
    (children : ∀ (pair : Pair), pair ∈ request.left.children.zip request.right.children →
      ∀ (used childFuel childCount : Nat),
      0 < used → childFuel < parentFuel → used + childFuel ≤ parentFuel →
      childCount ≤ childFuel → used + childCount ≤ bodySteps + 1 →
      ∀ (next : Node → Code Symbol Guard Row) (first last : Checked width) (value : Node),
      Steps used (.code (.edge request .pure)) original
        (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
      Physical first.native → Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      InputsThrough childFuel (.code (requestNode request.domain pair.1 pair.2)) first →
      FieldsThrough childFuel (.code (requestNode request.domain pair.1 pair.2)) first →
      Available first.native.machine.heap pair.1 → Available first.native.machine.heap pair.2 →
      Steps childCount (.code (requestNode request.domain pair.1 pair.2)) first
        (.code (.pure value)) last → Profile sourceName value)
    (jobs : List Pair) (before : Checked width) (values : List Node) (after : Checked width) (count : Nat)
    (walked : SourceEqualityNativeDemandWalkExecution.Walk
      (fun pair : Pair => requestNode request.domain pair.1 pair.2) jobs before values after count)
    (used : Nat) (next : List Node → Code Symbol Guard Row)
    (origin : Steps used (.code (.edge request .pure)) original
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestNode request.domain pair.1 pair.2) jobs).bind next)) before)
    (positive : 0 < used) (bounded : used + count ≤ parentFuel)
    (rawBound : used + count ≤ bodySteps + 1) (physical : Physical before.native)
    (included : ∀ pair ∈ jobs, pair ∈ request.left.children.zip request.right.children) :
    Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      (∀ value ∈ values, Available after.native.machine.heap value) ∧
      All₂ (fun _ value => Profile sourceName value) jobs values := by
  induction walked generalizing used next with
  | nil current =>
      exact ⟨physical, Extension.refl _, (by intro value member; cases member), .nil⟩
  | cons pair rest before middle after value values firstCount restCount called tail ih =>
      let childNext : Node → Code Symbol Guard Row := fun value =>
        (SourceRecursiveIntersectionCode.walk
          (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
            (fun values => next (value :: values))
      have atChild : Steps used (.code (.edge request .pure)) original
          (.code ((requestNode request.domain pair.1 pair.2).bind childNext)) before := by
        simpa only [SourceRecursiveIntersectionCode.walk, Code.bind_assoc, Code.bind, childNext] using origin
      have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        parentFuel used (.code (.edge request .pure))
        (.code (requestNode request.domain pair.1 pair.2)) childNext
        original before sourceHeap physicalOriginal plan fields operationsValid sourceGrowth atChild (by omega)
      obtain ⟨_checkedPrefix, childPhysical, _prefixExtension, childGrowth, childOperations,
        _operationGrowth, _boundPlan, childPlan, _boundFields, childFields⟩ := reached
      have ready := through_head (parentFuel - used)
        (.code (requestNode request.domain pair.1 pair.2)) before childPlan
      have own := children pair (included pair List.mem_cons_self) used (parentFuel - used) firstCount
        positive (by omega) (by omega) (by omega) (by omega) childNext before middle value atChild
        childPhysical childGrowth childOperations childPlan childFields ready.1.2.1 ready.1.2.2 called
      have completed := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        (parentFuel - used) firstCount (.code (requestNode request.domain pair.1 pair.2))
        (.code (.pure value)) .pure before middle sourceHeap childPhysical childPlan childFields
        childOperations childGrowth called (by omega)
      obtain ⟨checkedQuery, middlePhysical, queryExtension, _middleGrowth, _middleOperations,
        _queryOperationGrowth, _queryBoundPlan, _queryPlan, _queryBoundFields, _queryFields⟩ := completed
      have available := SourceCurrentNativeOpenRequestResults.node_result firstCount
        ⟨request.domain, pair.1, pair.2⟩ before middle value childPhysical checkedQuery
      have advanced := called.bind _ _ _ _ _ childNext
      have tailOrigin : Steps (used + firstCount) (.code (.edge request .pure)) original
          (.code ((SourceRecursiveIntersectionCode.walk
            (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
              (fun values => next (value :: values)))) middle :=
        atChild.trans _ _ _ _ _ _ _ _ advanced
      have restIncluded : ∀ candidate ∈ rest, candidate ∈ request.left.children.zip request.right.children := by
        intro candidate present
        exact included candidate (List.mem_cons_of_mem _ present)
      have later := ih (used + firstCount) (fun values => next (value :: values)) tailOrigin
        (by omega) (by omega) (by omega) middlePhysical restIncluded
      refine ⟨later.1, queryExtension.trans later.2.1, ?_, .cons own later.2.2.2⟩
      intro selected present
      cases present with
      | head => exact later.2.1.available value available
      | tail _ present => exact later.2.2.1 selected present

/-- A returned checked edge body derives every child Profile from its actual smaller node queries. -/
theorem edge_body_children_profile_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard) (sourceName : Nat)
    (request : EdgeRequest Symbol Guard) (original before after : Checked width)
    (parentFuel bodySteps : Nat) (result : Row)
    (finishNext : Row → Code Symbol Guard Row)
    (physical : Physical original.native) (sourceGrowth : Grows sourceHeap original.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid original.operations)
    (plan : InputsThrough parentFuel (.code (.edge request .pure)) original)
    (fields : FieldsThrough parentFuel (.code (.edge request .pure)) original)
    (entered : Steps 1 (.code (.edge request .pure)) original (.edgeBody request finishNext) before)
    (smaller : bodySteps < parentFuel)
    (actual : Steps bodySteps (.edgeBody request .pure) before (.code (.pure result)) after)
    (children : ∀ (pair : Pair), pair ∈ request.left.children.zip request.right.children →
      ∀ (used childFuel childCount : Nat),
      0 < used → childFuel < parentFuel → used + childFuel ≤ parentFuel →
      childCount ≤ childFuel → used + childCount ≤ bodySteps + 1 →
      ∀ (next : Node → Code Symbol Guard Row) (first last : Checked width) (value : Node),
      Steps used (.code (.edge request .pure)) original
        (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
      Physical first.native → Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      InputsThrough childFuel (.code (requestNode request.domain pair.1 pair.2)) first →
      FieldsThrough childFuel (.code (requestNode request.domain pair.1 pair.2)) first →
      Available first.native.machine.heap pair.1 → Available first.native.machine.heap pair.2 →
      Steps childCount (.code (requestNode request.domain pair.1 pair.2)) first
        (.code (.pure value)) last → Profile sourceName value) :
    (∀ child ∈ result.children, Profile sourceName child) ∧ EdgeResident after.native.machine.heap result ∧
    Physical after.native ∧ Extension original.native.machine after.native.machine ∧
    Grows sourceHeap after.native.machine.heap ∧
    SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    SourceEqualityConstraintMemoAllocation.Grows original.operations after.operations ∧
    ((∃ started : Checked width,
        SourceEqualityNativeDemand.body request .pure before =
          .yielded (.code (SourceEqualityNativeCheckedCode.sentinel request.left)) started ∧
        bodySteps = 2 ∧ result.children = [.empty] ∧
        result = (run (makeEdge request.left.entry.key.symbol top [.empty]) started.native.machine.heap).1 ∧
        after = {started with native := advance started.native {started.native.machine with heap :=
          (run (makeEdge request.left.entry.key.symbol top [.empty]) started.native.machine.heap).2}}) ∨
      ∃ (started : Checked width) (first second combined : Allocated) (values : List Node)
        (middle : Checked width) (walkCount : Nat),
        SourceEqualityNativeDemand.body request .pure before =
          .yielded (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined)) started ∧
        SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints =
          .ok (some first) ∧
        SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints =
          .ok (some second) ∧
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
          request.left.children.length request.right.children.length before.operations).1 = .ok (.ready combined) ∧
        bodySteps = walkCount + 2 ∧
        SourceEqualityNativeDemandWalkExecution.Walk (fun pair : Pair => requestNode request.domain pair.1 pair.2)
          (request.left.children.zip request.right.children) started values middle walkCount ∧
        All₂ (fun _ value => Profile sourceName value)
          (request.left.children.zip request.right.children) values ∧
        (∀ value ∈ values, Available middle.native.machine.heap value) ∧ result.children = values ∧
        Steps walkCount (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined))
          started (.code (.work (makeEdge request.left.entry.key.symbol
            (SourceEqualityConjoinAllocation.readback combined) values) .pure)) middle ∧
        Steps 1 (.code (.work (makeEdge request.left.entry.key.symbol
          (SourceEqualityConjoinAllocation.readback combined) values) .pure)) middle (.code (.pure result)) after ∧
        result = (run (makeEdge request.left.entry.key.symbol
          (SourceEqualityConjoinAllocation.readback combined) values) middle.native.machine.heap).1 ∧
        after = {middle with native := advance middle.native {middle.native.machine with heap :=
          (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values)
            middle.native.machine.heap).2}})
 := by
  have bodyBound := actual.bind _ _ _ _ _ finishNext
  have finalPrefix := entered.trans _ _ _ _ _ _ _ _ bodyBound
  have atFinal : Steps (1 + bodySteps) (.code (.edge request .pure)) original
      ((Control.code (.pure result)).bind finishNext) after := by
    simpa only [Control.bind] using finalPrefix
  have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel (1 + bodySteps) (.code (.edge request .pure)) (.code (.pure result)) finishNext
    original after sourceHeap physical plan fields operationsValid sourceGrowth atFinal (by omega)
  obtain ⟨checkedWhole, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
    _boundPlan, _rawPlan, _boundFields, _rawFields⟩ := reached
  have separated := SourceCurrentHereditaryNativePhysicalSplit.split entered checkedWhole
  have bodyTrace := SourceCurrentHereditaryNativePhysicalSplit.unbind actual finishNext separated.2
  obtain ⟨code, started, rest, bodyCount, one, tail⟩ :=
    protected_body_first request bodySteps before after result bodyTrace
  have firstStep : Steps 1 (.edgeBody request .pure) before (.code code) started :=
    .cons _ _ _ _ _ _ 0 one (.refl _ _)
  have startedPrefix := entered.trans _ _ _ _ _ _ _ _ (firstStep.bind _ _ _ _ _ finishNext)
  have atStarted : Steps 2 (.code (.edge request .pure)) original
      ((Control.code code).bind finishNext) started := by
    simpa only [Control.bind] using startedPrefix
  have startedResources := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel 2 (.code (.edge request .pure)) (.code code) finishNext
    original started sourceHeap physical plan fields operationsValid sourceGrowth atStarted (by omega)
  obtain ⟨_checkedStart, startedPhysical, _startedExtension, _startedGrowth, _startedOperations,
    _startedOperationGrowth, _startedBoundPlan, _startedPlan, _startedBoundFields, _startedFields⟩ := startedResources
  obtain ⟨_nativeSame, branch⟩ :=
    SourcePruningEnumerationNativeCheckedOriginArity.body_choice_checked request before started code one
  rcases branch with sentinelSame | ⟨first, second, combined, firstLoad, secondLoad, accepted, codeSame⟩
  · have workTrace : Trace rest
        (.code (.work (makeEdge request.left.entry.key.symbol top [.empty]) .pure)) started
        (.code (.pure result)) after := by
      simpa only [sentinelSame, SourceEqualityNativeCheckedCode.sentinel] using tail
    obtain ⟨workCount, sameResult, sameAfter, _workInputs⟩ :=
      SourceCurrentAllocatedNativeSemanticTraceReadback.work_readback
        (makeEdge request.left.entry.key.symbol top [.empty]) rest started after result workTrace
    have valuesAvailable : ∀ value ∈ ([.empty] : List Node), Available started.native.machine.heap value := by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact empty_available _
    have fieldsRead := MergedPhysicalGroupEdges.makeEdge_fields started.native.machine.heap
      startedPhysical.machine.1 request.left.entry.key.symbol top [.empty] valuesAvailable
    have shape : result.children = [.empty] := by
      rw [sameResult]
      exact fieldsRead.2.2
    have profiles : ∀ child ∈ result.children, Profile sourceName child := by
      intro child member
      rw [shape] at member
      have same := List.mem_singleton.mp member
      subst child
      exact empty_profile sourceName
    have verified := InternedNestedFacts.edge_verified request.left.entry.key.symbol top [.empty]
      started.native.machine.heap startedPhysical.machine.1 valuesAvailable
    have resident : EdgeResident after.native.machine.heap result := by
      rw [sameResult, sameAfter]
      exact verified.result _ _ rfl
    have branchOne : SourceEqualityNativeDemand.body request .pure before =
        .yielded (.code (SourceEqualityNativeCheckedCode.sentinel request.left)) started := by
      simpa only [sentinelSame] using one
    exact ⟨profiles, resident, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
      .inl ⟨started, branchOne, by omega, shape, sameResult, sameAfter⟩⟩
  · let call : Pair → Code Symbol Guard Node := fun pair => requestNode request.domain pair.1 pair.2
    let build : List Node → Code Symbol Guard Row := fun values =>
      .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure
    have acceptedTrace : Trace rest
        ((Control.code (SourceRecursiveIntersectionCode.walk call
          (request.left.children.zip request.right.children))).bind build) started
        (.code (.pure result)) after := by
      rw [codeSame] at tail
      exact tail
    obtain ⟨walkCount, workCount, values, middle, total, walkTrace, workTrace⟩ :=
      SourceCurrentHereditaryNativePhysicalSplit.bind_split
        (.code (SourceRecursiveIntersectionCode.walk call (request.left.children.zip request.right.children)))
        build started after result acceptedTrace
    have walked := SourceEqualityNativeDemandWalkExecution.trace_walk call
      (request.left.children.zip request.right.children) walkCount started middle values walkTrace.steps
    obtain ⟨workIsOne, sameResult, sameAfter, _workInputs⟩ :=
      SourceCurrentAllocatedNativeSemanticTraceReadback.work_readback
        (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values)
        workCount middle after result workTrace
    let finish : List Node → Code Symbol Guard Row := fun values => (build values).bind finishNext
    have walkOrigin : Steps 2 (.code (.edge request .pure)) original
        (.code ((SourceRecursiveIntersectionCode.walk call
          (request.left.children.zip request.right.children)).bind finish)) started := by
      rw [codeSame] at atStarted
      change Steps 2 (.code (.edge request .pure)) original
        (.code (((SourceRecursiveIntersectionCode.walk call
          (request.left.children.zip request.right.children)).bind build).bind finishNext)) started at atStarted
      simpa only [Code.bind_assoc] using atStarted
    have observed := walk_profiles sourceHeap sourceName request original parentFuel bodySteps
      physical sourceGrowth operationsValid plan fields children
      (request.left.children.zip request.right.children) started values middle walkCount walked
      2 finish walkOrigin (by omega) (by omega) (by omega) startedPhysical (by intros; assumption)
    have fieldsRead := MergedPhysicalGroupEdges.makeEdge_fields middle.native.machine.heap
      observed.1.machine.1 request.left.entry.key.symbol
      (SourceEqualityConjoinAllocation.readback combined) values observed.2.2.1
    have shape : result.children = values := by
      rw [sameResult]
      exact fieldsRead.2.2
    have profiles : ∀ child ∈ result.children, Profile sourceName child := by
      rw [shape]
      exact profiles_of_all_two sourceName observed.2.2.2
    have verified := InternedNestedFacts.edge_verified request.left.entry.key.symbol
      (SourceEqualityConjoinAllocation.readback combined) values middle.native.machine.heap
      observed.1.machine.1 observed.2.2.1
    have resident : EdgeResident after.native.machine.heap result := by
      rw [sameResult, sameAfter]
      exact verified.result _ _ rfl
    have throughWork : Steps walkCount
        (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined)) started
        (.code (.work (makeEdge request.left.entry.key.symbol
          (SourceEqualityConjoinAllocation.readback combined) values) .pure)) middle :=
      walked.trace.bind _ _ _ _ _ build
    have workStep : Steps 1
        (.code (.work (makeEdge request.left.entry.key.symbol
          (SourceEqualityConjoinAllocation.readback combined) values) .pure)) middle (.code (.pure result)) after := by
      simpa only [workIsOne] using workTrace.steps
    have branchOne : SourceEqualityNativeDemand.body request .pure before =
        .yielded (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined))
          started := by
      simpa only [codeSame] using one
    exact ⟨profiles, resident, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
      .inr ⟨started, first, second, combined, values, middle, walkCount,
        branchOne, firstLoad, secondLoad, accepted, by omega, walked, observed.2.2.2, observed.2.2.1,
        shape, throughWork, workStep, sameResult, sameAfter⟩⟩

end MicroCFTA.SourceCurrentAllocatedNativeCheckedEdgeBodyProfile
