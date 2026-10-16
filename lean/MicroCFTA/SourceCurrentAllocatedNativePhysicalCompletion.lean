import MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution
import MicroCFTA.SourceCurrentAllocatedNativeRunning

/-!
# Physical checked transitions for recursive completion

Physical memo validity suffices to retain loaded annotation fields.
Actual node and edge demands yield under strict independent request bounds.
The checked edge prefix derives its actual child code and field allocation.
These transition theorems do not assume a completed recursive body.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeFieldClosure (Fields OutcomeFields body_fields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "Heap" => SourceCurrentConjunctionEquality.Fields
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Initial physical caches and loaded fields contain no semantic result receipt. -/
structure Good (state : CheckedState width) : Prop where
  native : SourceCurrentAllocatedNativePhysicalCache.Valid state.native
  heap : SourceEqualityRequiredCache.Ready state.native.machine.heap
  operations : SourceEqualityConstraintMemoAllocation.Valid state.operations
  fields : Heap state.operations state.native.machine.heap

private theorem lift_native (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native = outcome.state := by cases outcome <;> rfl

/-- Actual source instructions retain field loads in the returned operation cache. -/
theorem step_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : CheckedState width)
    (valid : Good state) (heap : Heap state.operations state.native.machine.heap)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control state) (fields : Fields control state) :
    OutcomeFields (step control state) := by
  cases control with
  | edgeBody request next =>
      have growth := SourceEqualityNativeDemandOperations.body_operations request next state valid.operations
        (heap _ _ fields.1.2.1).1 (heap _ _ fields.1.2.2).1
      have retained : Heap (body request next state).state.operations (body request next state).state.native.machine.heap := by
        rw [SourceEqualityNativeDemandOperations.body_native]
        exact SourceCurrentConjunctionEquality.Fields.grows heap growth.2
      refine ⟨retained, ?_⟩
      cases one : body request next state with
      | yielded rest after =>
          simpa only [step, one] using body_fields request next state after rest heap fields.1 valid.operations fields.2 one
      | done | failed | constraintError | blocked => simp only [step, one]
  | code code =>
      cases code with
      | pure | fail => exact ⟨heap, trivial⟩
      | read name next => exact ⟨heap, fields _⟩
      | finishNode handle value next | finishEdge handle value next => exact ⟨heap, fields⟩
      | work job next =>
          exact ⟨SourceCurrentAllocatedNativeCodeFields.work_heap state.operations job state.native.machine.heap heap fields.1, fields.2 _⟩
      | enter domain left right first second next => exact ⟨heap, fields _⟩
      | optionalBinder pair value next =>
          have retained := SourceCurrentAllocatedNativeCodeFields.optionalBinder_heap state.operations pair value state.native.machine.heap
            valid.native.machine.1 heap inputs
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair value state.native.machine.heap with
          | done result after =>
              simp only [step, SourceRecursiveIntersectionNative.step, actual, lift, OutcomeFields, Outcome.state, advance, Fields]
              exact ⟨by simpa only [actual, InternedNestedConstruction.Outcome.state] using retained, fields _⟩
          | pending key after =>
              simp only [step, SourceRecursiveIntersectionNative.step, actual, lift, OutcomeFields, Outcome.state, advance]
              exact ⟨by simpa only [actual, InternedNestedConstruction.Outcome.state] using retained, trivial⟩
      | node request next =>
          have physical := SourceRecursiveIntersectionNative.node_step_machine SourceEqualityConstraintConstructors.top
            SourceEqualityPCSNativeEdge.conjoin request next state.native
          have retained : Heap (step (.code (.node request next)) state).state.operations (step (.code (.node request next)) state).state.native.machine.heap := by
            rw [SourceEqualityNativeDemandOperations.step_code_operations]
            change Heap state.operations (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) state.native)).state.native.machine.heap
            rw [lift_native, physical]
            exact heap
          refine ⟨retained, ?_⟩
          cases selected : lookupNode width request state.native with
          | mk selection chosen =>
              cases selection with
              | direct actual =>
                  simpa only [step, SourceRecursiveIntersectionNative.step, selected, lift, Fields] using
                    SourceCurrentAllocatedNativeCodeFields.fields_bind state.operations _ _
                      (SourceCurrentAllocatedNativeCodeFields.compileNode_fields state.operations actual) fields
              | memoized handle =>
                  cases demanded : demandNode handle chosen with
                  | mk observation current =>
                      cases observation with
                      | absent | busy => simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift]
                      | ready result =>
                          simpa only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, Fields] using fields result
                      | evaluate actual =>
                          simpa only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, Fields] using
                            SourceCurrentAllocatedNativeCodeFields.fields_bind state.operations _ (fun value => .finishNode handle value (next value))
                              (SourceCurrentAllocatedNativeCodeFields.compileNode_fields state.operations actual) (fun value => fields value)
      | edge request next =>
          have chosenValid := SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid state.native valid.native request inputs.1 inputs.2
          cases selected : lookupEdge width request state.native with
          | mk handle chosen =>
              have chosenMachine : chosen.machine = state.native.machine := by
                simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request state.native
              simp only [selected] at chosenValid
              have currentValid := SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid chosen chosenValid handle
              cases demanded : demandEdge handle chosen with
              | mk observation current =>
                  have currentMachine : current.machine = state.native.machine := by
                    have same := SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
                    simpa only [demanded, chosenMachine] using same
                  have retained : Heap state.operations current.machine.heap := by rw [currentMachine]; exact heap
                  simp only [demanded] at currentValid
                  cases observation with
                  | absent | busy =>
                      simp only [step, selected, demanded, OutcomeFields, Outcome.state]
                      exact ⟨retained, trivial⟩
                  | ready result =>
                      simp only [step, selected, demanded, OutcomeFields, Outcome.state, Fields]
                      exact ⟨retained, fields result⟩
                  | evaluate actual =>
                      have running := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen current actual demanded).2
                      simp only [step, selected, demanded, OutcomeFields, Outcome.state, Fields]
                      exact ⟨retained, (currentValid.edges.checked handle _ running).1, fields⟩

/-- One actual checked transition derives both physical and same-cache field invariants. -/
theorem step_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : CheckedState width) (valid : Good state)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control state) (fields : Fields control state) :
    Good (step control state).state ∧
      Extension state.native.machine (step control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (step control state).state.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations (step control state).state.operations ∧
      OutcomeFields (step control state) := by
  have physical := SourceCurrentAllocatedNativePhysicalExecution.step_invariants control state valid.native valid.heap inputs
  have operationFields := SourceCurrentAllocatedNativeFieldClosure.operation_fields control state valid.fields fields
  have operations := SourceEqualityNativeDemandOperations.step_operations control state valid.operations operationFields
  have annotations := step_fields control state valid valid.fields inputs fields
  exact ⟨⟨physical.1, physical.2.2.ready, operations.1, annotations.1⟩,
    physical.2.1, physical.2.2, operations.2, annotations⟩

private theorem operations_trans {before middle after : Operations}
    (first : SourceEqualityConstraintMemoAllocation.Grows before middle)
    (second : SourceEqualityConstraintMemoAllocation.Grows middle after) :
    SourceEqualityConstraintMemoAllocation.Grows before after :=
  ⟨SourceEqualityConstraintAllocation.steps_trans first.constraints second.constraints,
    Cache.extends_trans first.combinations second.combinations, Cache.extends_trans first.descents second.descents⟩

/-- Physical reached checks derive all cache invariants and actual continuation fields from the initial state. -/
theorem execute_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : CheckedState width) (valid : Good state)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel control state) (fields : Fields control state) :
    Good (SourceEqualityNativeDemand.execute fuel control state).state ∧
      Extension state.native.machine (SourceEqualityNativeDemand.execute fuel control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (SourceEqualityNativeDemand.execute fuel control state).state.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations (SourceEqualityNativeDemand.execute fuel control state).state.operations ∧
      OutcomeFields (SourceEqualityNativeDemand.execute fuel control state) := by
  induction fuel generalizing control state with
  | zero => exact ⟨valid, .refl _, SourceEqualityRequiredCache.pure_keeps _ valid.heap,
      SourceEqualityConstraintMemoAllocation.grows_refl _, valid.fields, fields⟩
  | succ fuel ih =>
      have one := step_invariants control state valid inputs.1 fields
      cases actual : step control state with
      | yielded next after =>
          have current : Good after ∧ Extension state.native.machine after.native.machine ∧
              SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
              SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations ∧ OutcomeFields (.yielded next after) := by
            simpa only [actual, Outcome.state] using one
          have rest := ih next after current.1
            (by simpa only [SourceCurrentAllocatedNativePhysicalExecution.InputsThrough, actual] using inputs.2)
            current.2.2.2.2.2
          simpa only [SourceEqualityNativeDemand.execute, actual] using And.intro rest.1
            ⟨current.2.1.trans rest.2.1, current.2.2.1.trans rest.2.2.1,
              operations_trans current.2.2.2.1 rest.2.2.2.1, rest.2.2.2.2⟩
      | done | failed | constraintError | blocked =>
          simpa only [SourceEqualityNativeDemand.execute, actual, Outcome.state] using one

private theorem yielded_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control Output) (state after : CheckedState width) (valid : Good state)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control state) (fields : Fields control state)
    (actual : step control state = .yielded next after) :
    Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations ∧ Fields next after := by
  have checked := step_invariants control state valid inputs fields
  have current : Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations ∧ OutcomeFields (.yielded next after) := by
    simpa only [actual, Outcome.state] using checked
  exact ⟨current.1, current.2.1, current.2.2.1, current.2.2.2.1, current.2.2.2.2.2⟩

/-- Strict source bounds exclude absent and busy observations at actual node demand. -/
theorem node_step_yields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard Output)
    (state : CheckedState width) (valid : Good state) (ready : NodeReady state.native.machine request)
    (active : SourceRecursiveIntersectionNative.ActiveAbove view holds bound state.native)
    (complete : Completes view (SourceRecursiveIntersectionNative.nodeSemantic request))
    (smaller : requiredFuel view (SourceRecursiveIntersectionNative.nodeSemantic request) complete < bound)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.node request next)))
    (fields : ∀ value, CodeFields state.operations (next value)) :
    ∃ control after, step (.code (.node request next)) state = .yielded control after ∧
      Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations ∧ Fields control after := by
  have finish := fun control after actual => yielded_invariants (.code (.node request next)) control state after
    valid ⟨ready, words⟩ fields actual
  cases selected : lookupNode width request state.native with
  | mk selection chosen =>
      cases selection with
      | direct original =>
          exact ⟨_, _, by simp only [step, SourceRecursiveIntersectionNative.step, selected, lift] <;> rfl, finish _ _ (by
            simp only [step, SourceRecursiveIntersectionNative.step, selected, lift] <;> rfl)⟩
      | memoized handle =>
          obtain ⟨key, requested, _, _⟩ := SourceRecursiveIntersectionNative.lookupNode_memoized request state.native chosen handle selected
          have safe := words key requested
          cases demanded : demandNode handle chosen with
          | mk observation current =>
              cases observation with
              | absent => exact False.elim (SourceRecursiveIntersectionNative.node_absent_impossible state.native chosen current
                  valid.native.shape request handle selected demanded)
              | busy => exact False.elim (SourceCurrentAllocatedNativePhysicalExecution.node_busy_impossible view holds bound
                  state.native chosen current valid.native active request ready safe complete smaller handle selected demanded)
              | ready value | evaluate original =>
                  exact ⟨_, _, by simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] <;> rfl, finish _ _ (by
                    simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] <;> rfl)⟩

/-- Strict source bounds exclude absent and busy observations at actual edge demand. -/
theorem edge_step_yields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : CheckedState width) (valid : Good state) (ready : EdgeReady state.native.machine request)
    (active : SourceRecursiveIntersectionNative.ActiveAbove view holds bound state.native)
    (complete : Completes view (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    (smaller : requiredFuel view (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete < bound)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code (.edge request next)))
    (fields : ∀ value, CodeFields state.operations (next value)) :
    ∃ control after, step (.code (.edge request next)) state = .yielded control after ∧
      Good after ∧ Extension state.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations ∧ Fields control after := by
  have finish := fun control after actual => yielded_invariants (.code (.edge request next)) control state after
    valid ⟨ready, words⟩ fields actual
  cases selected : lookupEdge width request state.native with
  | mk handle chosen =>
      cases demanded : demandEdge handle chosen with
      | mk observation current =>
          cases observation with
          | absent => exact False.elim (SourceRecursiveIntersectionNative.edge_absent_impossible state.native chosen current
              valid.native.shape request handle selected demanded)
          | busy => exact False.elim (SourceCurrentAllocatedNativePhysicalExecution.edge_busy_impossible view holds bound
              state.native chosen current valid.native active request ready words complete smaller handle selected demanded)
          | ready value | evaluate original =>
              exact ⟨_, _, by simp only [step, selected, demanded] <;> rfl, finish _ _ (by simp only [step, selected, demanded] <;> rfl)⟩

/-- Loaded original fields derive the actual checked prefix and its strictly bounded child program. -/
theorem body_prefix [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard)
    (scope : EdgeScope source request)
    (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request))
    (state : CheckedState width) (valid : Good state) (ready : EdgeReady state.native.machine request) :
    ∃ code operations,
      step (.edgeBody request .pure) state = .yielded (.code code) {state with operations := operations} ∧
      Good {state with operations := operations} ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations operations ∧
      CodeFields operations code ∧
      Safe code state.native.machine (fun after value => EdgeResident after.heap value) ∧
      SourceCurrentAllocatedNativeCodeProgress.Operands code state.native.machine ∧
      Below source holds (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete)
        code state.native.machine := by
  obtain ⟨code, operations, actual, operationValid, growth, heap, fields, safe, operands, bounded⟩ :=
    SourceCurrentAllocatedNativeCodeProgress.body_prefix source facts holds request scope complete state valid.native.machine ready
      valid.operations valid.fields
  exact ⟨code, operations, actual, ⟨valid.native, valid.heap, operationValid, heap⟩, growth, fields, safe, operands, bounded⟩


/-- A fresh literal pure source body completes and derives its physical result without a body-done premise. -/
theorem pure_miss_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : CheckedState width) (valid : Good state)
    (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : state.native.nodes.table key = none) (value : Value Symbol Guard)
    (pureBody : compileNode request = .pure value) :
    ∃ after, SourceEqualityNativeDemand.execute 3 (.code (requestNode request.domain request.left request.right)) state = .done value after ∧
      Steps 2 (.code (requestNode request.domain request.left request.right)) state (.code (.pure value)) after ∧
      SourceCurrentAllocatedNativePhysicalExecution.InputsThrough 3 (.code (requestNode request.domain request.left request.right)) state ∧
      Good after ∧ after.native.machine = state.native.machine ∧ after.operations = state.operations ∧
      Available after.native.machine.heap value := by
  have available : Available state.native.machine.heap value := by
    have certified := compileNode_safe request state.native.machine valid.native.machine ready
    simpa only [pureBody, Safe] using certified
  let handle := state.native.nodes.next
  let chosen := (lookupNode width request state.native).2
  let current := (demandNode handle chosen).2
  have selected : lookupNode width request state.native = (.memoized handle, chosen) := by
    simp [chosen, handle, lookupNode, requested, FlatMemoThunk.lookupOrInsert, missing]
  have demanded : demandNode handle chosen = (.evaluate request, current) := by
    apply Prod.ext
    · simp [chosen, handle, lookupNode, requested, FlatMemoThunk.lookupOrInsert, missing, demandNode, FlatMemoThunk.demand, Cache.put]
    · rfl
  have machine : current.machine = state.native.machine :=
    (SourceRecursiveIntersectionNative.demandNode_machine handle chosen).trans
      (SourceRecursiveIntersectionNative.lookupNode_machine request state.native)
  have currentAvailable : Available current.machine.heap value := by rw [machine]; exact available
  have running := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen current request demanded).2
  let after : CheckedState width := ⟨SourceRecursiveIntersectionThunks.finishNode handle value current, state.operations⟩
  have one : step (.code (requestNode request.domain request.left request.right)) state =
      .yielded (.code (.finishNode handle value (.pure value))) ⟨current, state.operations⟩ := by
    simp only [step, requestNode, SourceRecursiveIntersectionNative.step, selected, demanded, pureBody, Code.bind, lift]
  have two : step (.code (.finishNode handle value (.pure value))) (⟨current, state.operations⟩ : CheckedState width) =
      .yielded (.code (.pure value)) after := rfl
  have trace : Steps 2 (.code (requestNode request.domain request.left request.right)) state (.code (.pure value)) after :=
    .cons _ _ _ _ _ _ _ one (.cons _ _ _ _ _ _ _ two (.refl _ _))
  have plan : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough 3
      (.code (requestNode request.domain request.left request.right)) state := by
    refine ⟨⟨ready, fun _ _ => safe⟩, ?_⟩
    rw [one]
    refine ⟨⟨request, running, currentAvailable⟩, ?_⟩
    rw [two]
    exact ⟨trivial, trivial⟩
  have done := trace_done 2 _ state after value trace
  have checked := execute_invariants 3 _ state valid plan (fun _ => trivial)
  have finalGood : Good after := by simpa only [done, Outcome.state] using checked.1
  exact ⟨after, done, trace, plan, finalGood, machine, rfl, by simpa only [after, finishNode] using currentAvailable⟩

end MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion
