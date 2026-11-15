import MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
import MicroCFTA.SourceEqualityNativeDemandWalkExecution
import MicroCFTA.SourceEqualityNativeDemandAcceptedReadback
import MicroCFTA.SourceSynthesisCurrentUniverseAtomInductionSteps
import MicroCFTA.SourceSynthesisUniversePrefixHeight
import MicroCFTA.MergedColdReaderClosedInputs

/-!
# Closed native union distribution from actual smaller child queries

The original query prefix retains its actual continuation.
Every original member occurrence retains its ordered actual child trace.
Original plans derive each reached physical state and operand availability.
Native union construction combines closed original-universe profiles.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeClosedUnionProfile
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisUniversePrefixHeight (height)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid

set_option autoImplicit false

private theorem through_head
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (fuel : Nat) (control : Control Node) (state : Checked width)
    (plan : InputsThrough fuel control state) : Inputs control state := by
  cases fuel with
  | zero => exact plan
  | succ fuel => exact plan.1

private theorem union_code
    [DecidableEq Symbol]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (entry : Interned NodeKey) (members : List Node) (level : Nat) (free : List Reference)
    (other : Node) (side : Bool)
    (selected : decision domain.key
      (if side then .union entry members level free else other)
      (if side then other else .union entry members level free) =
        (if side then .leftUnion else .rightUnion)) :
    compileNode ⟨domain,
      if side then .union entry members level free else other,
      if side then other else .union entry members level free⟩ =
      (SourceRecursiveIntersectionCode.walk (fun member : Node =>
        requestNode domain (if side then member else other) (if side then other else member)) members).bind
        (fun values => .work (makeUnion values) .pure) := by
  cases side with
  | false =>
      change decision domain.key other (.union entry members level free) = .rightUnion at selected
      change compileNode ⟨domain, other, .union entry members level free⟩ =
        (SourceRecursiveIntersectionCode.walk (fun member : Node => requestNode domain other member) members).bind
          (fun values => .work (makeUnion values) .pure)
      simp only [compileNode, selected]
  | true =>
      change decision domain.key (.union entry members level free) other = .leftUnion at selected
      change compileNode ⟨domain, .union entry members level free, other⟩ =
        (SourceRecursiveIntersectionCode.walk (fun member : Node => requestNode domain member other) members).bind
          (fun values => .work (makeUnion values) .pure)
      simp only [compileNode, selected]

private theorem profiles_of_all_two {members values : List Node} (sourceName : Nat)
    (aligned : All₂ (fun _ value => Profile sourceName value) members values) :
    ∀ value ∈ values, Profile sourceName value := by
  induction aligned with
  | nil => intro value member; cases member
  | cons head tail ih =>
      intro value member
      cases member with
      | head => exact head
      | tail _ member => exact ih value member

private theorem walk_profiles
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard) (sourceName : Nat)
    (request : NodeRequest Symbol Guard) (original : Checked width) (parentFuel bodySteps : Nat)
    (physicalOriginal : Physical original.native) (sourceGrowth : Grows sourceHeap original.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid original.operations)
    (plan : InputsThrough parentFuel (.code (.node request .pure)) original)
    (fields : FieldsThrough parentFuel (.code (.node request .pure)) original)
    (children : ∀ (child : NodeRequest Symbol Guard) (used childFuel childCount : Nat),
      0 < used → childFuel < parentFuel → used + childFuel ≤ parentFuel →
      childCount ≤ childFuel → used + childCount ≤ bodySteps + 1 →
      child.domain = IntersectionEmptyDomain.emptyDomain →
      Profile sourceName child.left → Profile sourceName child.right →
      height child.left + height child.right < height request.left + height request.right →
      ∀ (next : Node → Code Symbol Guard Node) (first last : Checked width) (value : Node),
      Steps used (.code (.node request .pure)) original
        (.code ((requestNode child.domain child.left child.right).bind next)) first →
      Physical first.native → Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      InputsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      FieldsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      Available first.native.machine.heap child.left → Available first.native.machine.heap child.right →
      Steps childCount (.code (requestNode child.domain child.left child.right)) first
        (.code (.pure value)) last → Profile sourceName value)
    (child : Node → NodeRequest Symbol Guard) (members : List Node)
    (qualified : ∀ member ∈ members,
      (child member).domain = IntersectionEmptyDomain.emptyDomain ∧
      Profile sourceName (child member).left ∧ Profile sourceName (child member).right ∧
      height (child member).left + height (child member).right < height request.left + height request.right)
    (jobs : List Node) (before : Checked width) (values : List Node) (after : Checked width) (count : Nat)
    (walked : SourceEqualityNativeDemandWalkExecution.Walk (fun member : Node =>
      requestNode (child member).domain (child member).left (child member).right) jobs before values after count)
    (used : Nat) (next : List Node → Code Symbol Guard Node)
    (origin : Steps used (.code (.node request .pure)) original
      (.code ((SourceRecursiveIntersectionCode.walk (fun member : Node =>
        requestNode (child member).domain (child member).left (child member).right) jobs).bind next)) before)
    (positive : 0 < used) (bounded : used + count ≤ parentFuel)
    (rawBound : used + count ≤ bodySteps + 1) (physical : Physical before.native)
    (included : ∀ member ∈ jobs, member ∈ members) :
    Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      (∀ value ∈ values, Available after.native.machine.heap value) ∧
      All₂ (fun _ value => Profile sourceName value) jobs values := by
  induction walked generalizing used next with
  | nil current =>
      exact ⟨physical, Extension.refl _, (by intro value member; cases member), .nil⟩
  | cons member rest before middle after value values firstCount restCount called tail ih =>
      let childNext : Node → Code Symbol Guard Node := fun value =>
        (SourceRecursiveIntersectionCode.walk (fun member : Node =>
          requestNode (child member).domain (child member).left (child member).right) rest).bind
          (fun values => next (value :: values))
      have atChild : Steps used (.code (.node request .pure)) original
          (.code ((requestNode (child member).domain (child member).left (child member).right).bind childNext)) before := by
        simpa only [SourceRecursiveIntersectionCode.walk, Code.bind_assoc, Code.bind, childNext] using origin
      have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        parentFuel used (.code (.node request .pure))
        (.code (requestNode (child member).domain (child member).left (child member).right)) childNext
        original before sourceHeap physicalOriginal plan fields operationsValid sourceGrowth atChild (by omega)
      obtain ⟨_checkedPrefix, childPhysical, _prefixExtension, childGrowth, childOperations,
        _operationGrowth, _boundPlan, childPlan, _boundFields, childFields⟩ := reached
      have ready := through_head (parentFuel - used)
        (.code (requestNode (child member).domain (child member).left (child member).right)) before childPlan
      obtain ⟨domain, leftProfile, rightProfile, descent⟩ := qualified member (included member List.mem_cons_self)
      have own := children (child member) used (parentFuel - used) firstCount positive (by omega) (by omega)
        (by omega) (by omega) domain leftProfile rightProfile descent childNext before middle value atChild
        childPhysical childGrowth childOperations childPlan childFields ready.1.2.1 ready.1.2.2 called
      have completed := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        (parentFuel - used) firstCount
        (.code (requestNode (child member).domain (child member).left (child member).right))
        (.code (.pure value)) .pure before middle sourceHeap childPhysical childPlan childFields
        childOperations childGrowth called (by omega)
      obtain ⟨checkedQuery, middlePhysical, queryExtension, _middleGrowth, _middleOperations,
        _queryOperationGrowth, _queryBoundPlan, _queryPlan, _queryBoundFields, _queryFields⟩ := completed
      have available := SourceCurrentNativeOpenRequestResults.node_result
        firstCount (child member) before middle value childPhysical checkedQuery
      have advanced := called.bind _ _ _ _ _ childNext
      have tailOrigin : Steps (used + firstCount) (.code (.node request .pure)) original
          (.code ((SourceRecursiveIntersectionCode.walk (fun member : Node =>
            requestNode (child member).domain (child member).left (child member).right) rest).bind
            (fun values => next (value :: values)))) middle :=
        atChild.trans _ _ _ _ _ _ _ _ advanced
      have restIncluded : ∀ candidate ∈ rest, candidate ∈ members := by
        intro candidate present
        exact included candidate (List.mem_cons_of_mem _ present)
      have later := ih (used + firstCount) (fun values => next (value :: values)) tailOrigin
        (by omega) (by omega) (by omega) middlePhysical restIncluded
      refine ⟨later.1, queryExtension.trans later.2.1, ?_, .cons own later.2.2.2⟩
      intro selected present
      cases present with
      | head => exact later.2.1.available value available
      | tail _ present => exact later.2.2.1 selected present

/-- The actual closed union control case combines all ordered smaller child Profiles at its original endpoint. -/
theorem closed_union_body_profile_of_fuel_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard) (sourceName : Nat)
    (unionEntry : Interned NodeKey) (members : List Node) (level : Nat) (free : List Reference)
    (other : Node) (side : Bool)
    (unionProfile : Profile sourceName (.union unionEntry members level free))
    (otherProfile : Profile sourceName other) :
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,
      if side then .union unionEntry members level free else other,
      if side then other else .union unionEntry members level free⟩
    ∀ (original before after : Checked width) (parentFuel bodySteps : Nat) (result : Node)
      (finishNext : Node → Code Symbol Guard Node),
    Physical original.native → Grows sourceHeap original.native.machine.heap →
    SourceEqualityConstraintMemoAllocation.Valid original.operations →
    InputsThrough parentFuel (.code (.node request .pure)) original →
    FieldsThrough parentFuel (.code (.node request .pure)) original →
    decision request.domain.key request.left request.right = (if side then .leftUnion else .rightUnion) →
    Steps 1 (.code (.node request .pure)) original
      (.code ((compileNode request).bind finishNext)) before →
    bodySteps < parentFuel →
    Steps bodySteps (.code (compileNode request)) before (.code (.pure result)) after →
    (∀ (child : NodeRequest Symbol Guard) (used childFuel childCount : Nat),
      0 < used → childFuel < parentFuel → used + childFuel ≤ parentFuel →
      childCount ≤ childFuel → used + childCount ≤ bodySteps + 1 →
      child.domain = IntersectionEmptyDomain.emptyDomain →
      Profile sourceName child.left → Profile sourceName child.right →
      height child.left + height child.right < height request.left + height request.right →
      ∀ (next : Node → Code Symbol Guard Node) (first last : Checked width) (value : Node),
      Steps used (.code (.node request .pure)) original
        (.code ((requestNode child.domain child.left child.right).bind next)) first →
      Physical first.native → Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      InputsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      FieldsThrough childFuel (.code (requestNode child.domain child.left child.right)) first →
      Available first.native.machine.heap child.left → Available first.native.machine.heap child.right →
      Steps childCount (.code (requestNode child.domain child.left child.right)) first
        (.code (.pure value)) last → Profile sourceName value) →
    Profile sourceName result ∧ Available after.native.machine.heap result ∧ Physical after.native ∧
    Extension original.native.machine after.native.machine ∧ Grows sourceHeap after.native.machine.heap ∧
    SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    SourceEqualityConstraintMemoAllocation.Grows original.operations after.operations ∧
    ∃ (values : List Node) (middle : Checked width) (walkCount workCount : Nat),
      bodySteps = walkCount + workCount ∧
      SourceEqualityNativeDemandWalkExecution.Walk (fun member : Node =>
        requestNode request.domain (if side then member else other) (if side then other else member))
        members before values middle walkCount ∧
      All₂ (fun _ value => Profile sourceName value) members values ∧
      (∀ value ∈ values, Available middle.native.machine.heap value) ∧
      Steps walkCount (.code (compileNode request)) before
        (.code (.work (makeUnion values) .pure)) middle ∧
      Steps workCount (.code (.work (makeUnion values) .pure)) middle (.code (.pure result)) after ∧
      result = (run (makeUnion values) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeUnion values) middle.native.machine.heap).2}} := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,
    if side then .union unionEntry members level free else other,
    if side then other else .union unionEntry members level free⟩
  dsimp only
  intro original before after parentFuel bodySteps result finishNext
    physical sourceGrowth operationsValid plan fields selected entered smaller actual children
  change Steps 1 (Control.code (.node request .pure)) original
    (Control.code ((compileNode request).bind finishNext)) before at entered
  change Steps bodySteps (Control.code (compileNode request)) before
    (Control.code (.pure result)) after at actual
  let child : Node → NodeRequest Symbol Guard := fun member => ⟨request.domain,
    if side then member else other, if side then other else member⟩
  let build : List Node → Code Symbol Guard Node := fun values => .work (makeUnion values) .pure
  have compiled : compileNode request =
      (SourceRecursiveIntersectionCode.walk (fun member : Node =>
        requestNode (child member).domain (child member).left (child member).right) members).bind build :=
    union_code IntersectionEmptyDomain.emptyDomain unionEntry members level free other side selected
  have current := through_head parentFuel (.code (.node request .pure)) original plan
  have unionAvailable : Available original.native.machine.heap (.union unionEntry members level free) := by
    cases side with
    | false => exact current.1.2.2
    | true => exact current.1.2.1
  have memberFacts := SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms
    original.native.machine.heap physical.machine.1 sourceName unionEntry members level free
    unionAvailable unionProfile.1 unionProfile.2
  have qualified : ∀ member ∈ members,
      (child member).domain = IntersectionEmptyDomain.emptyDomain ∧
      Profile sourceName (child member).left ∧ Profile sourceName (child member).right ∧
      height (child member).left + height (child member).right < height request.left + height request.right := by
    intro member present
    obtain ⟨_available, closed, onlyU⟩ := memberFacts member present
    have memberProfile : Profile sourceName member := ⟨closed, onlyU⟩
    have descent := SourceSynthesisUniversePrefixHeight.member_lt unionEntry members level free member present
    cases side with
    | false => exact ⟨rfl, otherProfile, memberProfile, Nat.add_lt_add_left descent (height other)⟩
    | true => exact ⟨rfl, memberProfile, otherProfile, Nat.add_lt_add_right descent (height other)⟩
  have raw : Steps bodySteps
      ((Control.code (SourceRecursiveIntersectionCode.walk (fun member : Node =>
        requestNode (child member).domain (child member).left (child member).right) members)).bind build)
      before (.code (.pure result)) after := by
    simpa only [compiled, Control.bind] using actual
  obtain ⟨walkCount, workCount, values, middle, total, walkedTrace, workTrace⟩ := steps_bind_inverse bodySteps
    (.code (SourceRecursiveIntersectionCode.walk (fun member : Node =>
      requestNode (child member).domain (child member).left (child member).right) members))
    build before after result raw
  have workPositive : 0 < workCount := by
    by_cases zero : workCount = 0
    · subst workCount
      cases (steps_zero _ _ _ _ workTrace).1
    · omega
  have walked := SourceEqualityNativeDemandWalkExecution.trace_walk
    (fun member : Node => requestNode (child member).domain (child member).left (child member).right)
    members walkCount before middle values walkedTrace
  have firstReached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel 1 (.code (.node request .pure)) (.code (compileNode request)) finishNext
    original before sourceHeap physical plan fields operationsValid sourceGrowth entered (by omega)
  have firstPhysical := firstReached.2.1
  let fullNext : List Node → Code Symbol Guard Node := fun values => (build values).bind finishNext
  have walkOrigin : Steps 1 (.code (.node request .pure)) original
      (.code ((SourceRecursiveIntersectionCode.walk (fun member : Node =>
        requestNode (child member).domain (child member).left (child member).right) members).bind fullNext)) before := by
    simpa only [compiled, Code.bind_assoc, fullNext] using entered
  have observed := walk_profiles sourceHeap sourceName request original parentFuel bodySteps
    physical sourceGrowth operationsValid plan fields children child members qualified
    members before values middle walkCount walked 1 fullNext walkOrigin (by decide) (by omega) (by omega)
    firstPhysical (by intro member present; exact present)
  have allProfiles := profiles_of_all_two sourceName observed.2.2.2
  have builtProfile : Profile sourceName (run (makeUnion values) middle.native.machine.heap).1 := by
    refine ⟨MergedColdReaderClosedInputs.makeUnion_closed values middle.native.machine.heap
      observed.1.machine.1 observed.2.2.1 (fun value present => (allProfiles value present).1), ?_⟩
    intro atom occurrence
    obtain ⟨value, present, included⟩ := InternedBoundaryAtoms.makeUnion_atom_origin values
      middle.native.machine.heap observed.1.machine.1.coherent observed.1.machine.1.cached
      observed.1.machine.1.linked observed.2.2.1 atom occurrence
    exact (allProfiles value present).2 atom included
  have throughWork : Steps walkCount (.code (compileNode request)) before
      (.code (.work (makeUnion values) .pure)) middle := by
    have appended := walkedTrace.bind _ _ _ _ _ build
    simpa only [compiled, Control.bind, build, Code.bind] using appended
  have workFields := SourceEqualityNativeDemandAcceptedReadback.work_observation
    (makeUnion values) (workCount + 1) middle after result
    (trace_done workCount _ middle after result workTrace)
  have verified := InternedNestedFacts.union_verified values middle.native.machine.heap
    observed.1.machine.1 observed.2.2.1
  have available : Available after.native.machine.heap result := by
    rw [workFields.1, workFields.2]
    exact verified.result _ _ rfl
  have profile : Profile sourceName result := by
    rw [workFields.1]
    exact builtProfile
  have bodyBound := actual.bind _ _ _ _ _ finishNext
  have finalPrefix := entered.trans _ _ _ _ _ _ _ _ bodyBound
  have atFinal : Steps (1 + bodySteps) (.code (.node request .pure)) original
      ((Control.code (.pure result)).bind finishNext) after := by
    simpa only [Control.bind] using finalPrefix
  have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel (1 + bodySteps) (.code (.node request .pure)) (.code (.pure result)) finishNext
    original after sourceHeap physical plan fields operationsValid sourceGrowth atFinal (by omega)
  obtain ⟨_checked, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
    _boundPlan, _rawPlan, _boundFields, _rawFields⟩ := reached
  exact ⟨profile, available, afterPhysical, extension, afterGrowth, afterOperations, operationGrowth,
    values, middle, walkCount, workCount, total.symm, walked, observed.2.2.2, observed.2.2.1,
    throughWork, workTrace, workFields.1, workFields.2⟩

end MicroCFTA.SourceCurrentAllocatedNativeClosedUnionProfile
