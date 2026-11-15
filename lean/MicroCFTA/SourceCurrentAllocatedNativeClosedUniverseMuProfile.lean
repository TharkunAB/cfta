import MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
import MicroCFTA.SourceCurrentAllocatedNativeMuSource
import MicroCFTA.SourceCurrentNativeOpenRequestResults
import MicroCFTA.SourceSynthesisUniverseClosedResetSteps
import MicroCFTA.SourceEqualityNativeDemandTraceSplit

/-!
# The actual closed parent Mu body and its original mixed child

This selected C case retains the full stored universe and pattern.
The C parent supplies Profile for its other operand.
The global original-M clause does not gain that premise.
Both operand orders allocate the same literal original domain.
The real ordered entry event and all raw counts remain explicit.
A closed child leaves the optional binder and complete state unchanged.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeClosedUniverseMuProfile
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity tag)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceSynthesisUniversePrefixHeight (height)
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

private theorem closed_optional_trace
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (binder : Nat × Nat) (value : Node) (before after : Checked width)
    (count : Nat) (result : Node) (closed : value.free = [])
    (actual : Steps count (.code (.optionalBinder binder value .pure)) before (.code (.pure result)) after) :
    count = 1 ∧ result = value ∧ after = before := by
  have absent : Reference.intersection binder.1 binder.2 ∉ value.free := by
    rw [closed]
    exact List.not_mem_nil
  have unused := SourceRecursiveIntersectionMaybeMu.unused binder value before.native.machine.heap absent
  have one : SourceEqualityNativeDemand.step (.code (.optionalBinder binder value .pure)) before =
      .yielded (.code (.pure value))
        {before with native := advance before.native {before.native.machine with heap := before.native.machine.heap}} := by
    simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
      unused, SourceEqualityNativeDemand.lift]
  cases count with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (chosen.symm.trans one)
      have terminal := pure_trace remaining value result
        {before with native := advance before.native {before.native.machine with heap := before.native.machine.heap}} after tail
      have remainingZero : remaining = 0 := terminal.1
      exact ⟨by omega, terminal.2.1.symm, terminal.2.2.symm⟩

/-- The actual selected closed Mu body uses its admitted original mixed child and returns the same closed value. -/
theorem closed_universe_mu_profile_trace_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (universeClosed : (Value.mu entry body depth ordinary).free = [])
    (pattern : Node) (patternProfile : Profile entry.identity pattern)
    (patternId : Nat) (patternIdentity : identity pattern = some patternId)
    (patternKind : tag pattern = 1 ∨ tag pattern = 3) (leftIsU : Bool)
    (original before after : Checked width) (parentFuel bodySteps : Nat) (result : Node)
    (finishNext : Node → Code Symbol Guard Node)
    (physical : Physical original.native)
    (sourceGrowth : Grows sourceHeap original.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid original.operations) :
    let universeValue : Node := .mu entry body depth ordinary
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,
      if leftIsU then universeValue else pattern, if leftIsU then pattern else universeValue⟩
    let childLeft := if leftIsU then body else pattern
    let childRight := if leftIsU then pattern else body
    let first := if leftIsU then entry.identity else patternId
    let second := if leftIsU then patternId else entry.identity
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    let started : Checked width :=
      {before with native := advance before.native {before.native.machine with domains := entered.2}}
    let binder := SourceRecursiveIntersectionControl.pair entry.identity patternId
    let enterNext := fun domain => (requestNode domain childLeft childRight).bind
      (fun value => .optionalBinder binder value .pure)
    SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right =
      (if leftIsU then .leftMu else .rightMu) →
    InputsThrough parentFuel (.code (.node request .pure)) original →
    FieldsThrough parentFuel (.code (.node request .pure)) original →
    Steps 1 (.code (.node request .pure)) original
      (.code ((compileNode request).bind finishNext)) before →
    bodySteps < parentFuel →
    Steps bodySteps (.code (compileNode request)) before (.code (.pure result)) after →
    (∀ (childFuel childCount : Nat), childFuel < parentFuel → childCount ≤ childFuel →
      2 + childFuel ≤ parentFuel → 2 + childCount ≤ parentFuel →
      ∀ (next : Node → Code Symbol Guard Node) (value : Node) (middle : Checked width),
      Steps 2 (.code (.node request .pure)) original
        (.code ((requestNode entered.1 childLeft childRight).bind next)) started →
      Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain request.left request.right
        first second enterNext)) before (.code (enterNext entered.1)) started →
      Physical started.native → Grows sourceHeap started.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid started.operations →
      InputsThrough childFuel (.code (requestNode entered.1 childLeft childRight)) started →
      FieldsThrough childFuel (.code (requestNode entered.1 childLeft childRight)) started →
      Domain started.native.machine entered.1 →
      Available started.native.machine.heap childLeft → Available started.native.machine.heap childRight →
      universeValue.free = [] → Profile entry.identity pattern → height pattern ≤ height pattern →
      Steps childCount (.code (requestNode entered.1 childLeft childRight)) started
        (.code (.pure value)) middle → Profile entry.identity value) →
    Profile entry.identity result ∧ Available after.native.machine.heap result ∧ Physical after.native ∧
    Extension original.native.machine after.native.machine ∧ Grows sourceHeap after.native.machine.heap ∧
    SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    SourceEqualityConstraintMemoAllocation.Grows original.operations after.operations ∧
    SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right first second = entered ∧
    entered.1.key.free.isEmpty = false ∧
    ∃ (childCount : Nat) (middle : Checked width),
      bodySteps = 1 + childCount + 1 ∧ 2 + childCount ≤ parentFuel ∧ childCount < parentFuel ∧
      Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain request.left request.right
        first second enterNext)) before (.code (enterNext entered.1)) started ∧
      Steps 2 (.code (.node request .pure)) original
        (.code ((requestNode entered.1 childLeft childRight).bind
          (fun value => .optionalBinder binder value finishNext))) started ∧
      Steps childCount (.code (requestNode entered.1 childLeft childRight)) started
        (.code (.pure result)) middle ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu binder result middle.native.machine.heap =
        .done result middle.native.machine.heap ∧
      Steps 1 (.code (.optionalBinder binder result .pure)) middle (.code (.pure result)) after ∧
      after = middle := by
  let universeValue : Node := .mu entry body depth ordinary
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,
    if leftIsU then universeValue else pattern, if leftIsU then pattern else universeValue⟩
  let childLeft := if leftIsU then body else pattern
  let childRight := if leftIsU then pattern else body
  let first := if leftIsU then entry.identity else patternId
  let second := if leftIsU then patternId else entry.identity
  let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let started : Checked width :=
    {before with native := advance before.native {before.native.machine with domains := entered.2}}
  let binder := SourceRecursiveIntersectionControl.pair entry.identity patternId
  let query := requestNode entered.1 childLeft childRight
  let next : Node → Code Symbol Guard Node := fun value => .optionalBinder binder value .pure
  let enterNext := fun domain => (requestNode domain childLeft childRight).bind next
  let lifted : Node → Code Symbol Guard Node := fun value => (next value).bind finishNext
  dsimp only
  intro selected plan fields dispatched smaller actual children
  have patternBody : SourceRecursiveIntersectionKernel.body pattern = pattern := by
    cases pattern <;> try rfl
    simp [tag] at patternKind
  have patternBinder : SourceRecursiveIntersectionEnvironment.binder pattern = [] := by
    cases pattern <;> try rfl
    simp [tag] at patternKind
  have pairReverse : SourceRecursiveIntersectionControl.pair patternId entry.identity = binder := by
    change SourceRecursiveIntersectionControl.pair patternId entry.identity =
      SourceRecursiveIntersectionControl.pair entry.identity patternId
    simp only [SourceRecursiveIntersectionControl.pair, Nat.min_comm, Nat.max_comm]
  have enterReverse :
      SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains IntersectionEmptyDomain.emptyKey
        pattern universeValue patternId entry.identity = entered := by
    change IntersectionEmptyDomain.make before.native.machine.domains
      (SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
        ((SourceRecursiveIntersectionEnvironment.binder pattern ++
          SourceRecursiveIntersectionEnvironment.binder universeValue).map Prod.fst)
        (SourceRecursiveIntersectionControl.pair patternId entry.identity)) =
      IntersectionEmptyDomain.make before.native.machine.domains
        (SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
          ((SourceRecursiveIntersectionEnvironment.binder universeValue ++
            SourceRecursiveIntersectionEnvironment.binder pattern).map Prod.fst)
          (SourceRecursiveIntersectionControl.pair entry.identity patternId))
    rw [patternBinder]
    simp only [List.nil_append, List.append_nil, pairReverse, binder]
  have allocatedEq :
      SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
        request.left request.right first second = entered := by
    cases leftIsU with
    | false => exact enterReverse
    | true => rfl
  have leftIdentity : identity request.left = some first := by
    cases leftIsU with
    | false => exact patternIdentity
    | true => rfl
  have rightIdentity : identity request.right = some second := by
    cases leftIsU with
    | false => rfl
    | true => exact patternIdentity
  have bodyLeft : SourceRecursiveIntersectionKernel.body request.left = childLeft := by
    cases leftIsU with
    | false => exact patternBody
    | true => rfl
  have bodyRight : SourceRecursiveIntersectionKernel.body request.right = childRight := by
    cases leftIsU with
    | false => rfl
    | true => exact patternBody
  have binderEq : SourceRecursiveIntersectionControl.pair first second = binder := by
    cases leftIsU with
    | false => exact pairReverse
    | true => rfl
  have compiledMu : compileNode request = compileMu request.domain request.left request.right := by
    cases leftIsU with
    | false =>
        have chosen : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu := selected
        simp only [compileNode, chosen]
    | true =>
        have chosen : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu := selected
        simp only [compileNode, chosen]
  have authenticCode : compileNode request =
      .enter IntersectionEmptyDomain.emptyDomain request.left request.right first second enterNext := by
    rw [compiledMu]
    simp only [compileMu, leftIdentity, rightIdentity, bodyLeft, bodyRight, binderEq]
    rfl
  have one : SourceEqualityNativeDemand.step (.code (compileNode request)) before =
      .yielded (.code (query.bind next)) started := by
    rw [compiledMu]
    have nativeOne := SourceCurrentAllocatedNativeMuSource.enter_prefix
      request before first second leftIdentity rightIdentity
    dsimp only at nativeOne
    rw [allocatedEq, bodyLeft, bodyRight, binderEq] at nativeOne
    exact nativeOne
  have origin : Steps 1 (.code (compileNode request)) before (.code (query.bind next)) started :=
    .cons _ _ _ _ _ _ _ one (.refl _ _)
  have outer : Steps 2 (.code (.node request .pure)) original (.code (query.bind lifted)) started := by
    have composed := dispatched.trans _ _ _ _ _ _ _ _ (origin.bind _ _ _ _ _ finishNext)
    simpa only [Control.bind, Code.bind_assoc, Code.bind, lifted] using composed
  have beforeScope := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    parentFuel 1 (.code (.node request .pure)) (.code (compileNode request)) finishNext
    original before sourceHeap physical plan fields operationsValid sourceGrowth dispatched (by omega)
  obtain ⟨_dispatchChecked, beforePhysical, beforeExtension, beforeGrowth, beforeOperations,
    _beforeOperationsGrowth, _boundBodyPlan, bodyPlan, _boundBodyFields, bodyFields⟩ := beforeScope
  have nonempty : entered.1.key.free.isEmpty = false :=
    SourceSynthesisUniverseClosedResetSteps.mixed_entry_nonempty_free_map
      before.native.machine.domains beforePhysical.machine.2 entry body depth ordinary pattern patternId
  have universeAvailable : Available original.native.machine.heap universeValue :=
    physical.machine.1.cached.nodes key _ (sourceGrowth.nodeRecords key _ stored)
  have bodyAvailable : Available original.native.machine.heap body :=
    universeAvailable.children body (by simp [universeValue, InternedProbeProvenance.children])
  have originalInputs := through_head parentFuel (.code (.node request .pure)) original plan
  have patternAvailable : Available original.native.machine.heap pattern := by
    cases leftIsU with
    | false => exact originalInputs.1.2.1
    | true => exact originalInputs.1.2.2
  cases bodySteps with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (chosen.symm.trans one)
      obtain ⟨childCount, optionalCount, value, middle, splitCount, childTrace, optionalTrace⟩ :=
        steps_bind_inverse remaining (.code query) next started after result tail
      have startedScope := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        (parentFuel - 1) 1 (.code (compileNode request)) (.code query) next before started sourceHeap
        beforePhysical bodyPlan bodyFields beforeOperations beforeGrowth origin (by omega)
      obtain ⟨entryChecked, startedPhysical, enterExtension, startedGrowth, startedOperations,
        _startedOperationsGrowth, _boundChildPlan, childPlan, _boundChildFields, childFields⟩ := startedScope
      have authenticEntry : Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain request.left request.right
          first second enterNext)) before (.code (enterNext entered.1)) started := by
        rw [← authenticCode]
        exact entryChecked
      have startedExtension := beforeExtension.trans enterExtension
      have startedBody := startedExtension.available body bodyAvailable
      have startedPattern := startedExtension.available pattern patternAvailable
      have leftAvailable : Available started.native.machine.heap childLeft := by
        cases leftIsU with
        | false => exact startedPattern
        | true => exact startedBody
      have rightAvailable : Available started.native.machine.heap childRight := by
        cases leftIsU with
        | false => exact startedBody
        | true => exact startedPattern
      have childInputs := through_head ((parentFuel - 1) - 1) (.code query) started childPlan
      have childProperty : Profile entry.identity value :=
        children ((parentFuel - 1) - 1) childCount (by omega) (by omega) (by omega) (by omega)
          lifted value middle outer authenticEntry startedPhysical startedGrowth startedOperations
          childPlan childFields childInputs.1.1 leftAvailable rightAvailable
          universeClosed patternProfile (Nat.le_refl _) childTrace
      obtain ⟨optionalSteps, resultEq, endpoint⟩ :=
        closed_optional_trace binder value middle after optionalCount result childProperty.1 optionalTrace
      subst result
      have childToPure : Steps childCount (.code query) started
          ((.code (.pure value) : Control Node).bind (fun returned => .pure returned)) middle := by
        simpa only [Control.bind, Code.bind] using childTrace
      have childScope := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        ((parentFuel - 1) - 1) childCount (.code query) (.code (.pure value)) (fun returned => .pure returned)
        started middle sourceHeap startedPhysical childPlan childFields startedOperations startedGrowth
        childToPure (by omega)
      have checkedChild : Trace childCount (.code query) started (.code (.pure value)) middle := by
        simpa only [Control.bind, Code.bind] using childScope.1
      have available := SourceCurrentNativeOpenRequestResults.node_result
        childCount ⟨entered.1, childLeft, childRight⟩ started middle value startedPhysical checkedChild
      have fullPrefix : Steps (1 + Nat.succ remaining) (.code (.node request .pure)) original
          ((.code (.pure value) : Control Node).bind finishNext) after := by
        have composed := dispatched.trans _ _ _ _ _ _ _ _ (actual.bind _ _ _ _ _ finishNext)
        simpa only [Control.bind, Code.bind] using composed
      have fullScope := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        parentFuel (1 + Nat.succ remaining) (.code (.node request .pure)) (.code (.pure value)) finishNext
        original after sourceHeap physical plan fields operationsValid sourceGrowth fullPrefix (by omega)
      obtain ⟨_fullChecked, afterPhysical, afterExtension, afterGrowth, afterOperations,
        afterOperationsGrowth, _boundResultPlan, _resultPlan, _boundResultFields, _resultFields⟩ := fullScope
      refine ⟨childProperty, ?_, afterPhysical, afterExtension, afterGrowth, afterOperations,
        afterOperationsGrowth, allocatedEq, nonempty, childCount, middle, by omega, by omega,
        by omega, authenticEntry, outer, childTrace, ?_, ?_, endpoint⟩
      · rw [endpoint]
        exact available
      · apply SourceRecursiveIntersectionMaybeMu.unused
        rw [childProperty.1]
        exact List.not_mem_nil
      · simpa only [optionalSteps] using optionalTrace

end MicroCFTA.SourceCurrentAllocatedNativeClosedUniverseMuProfile
