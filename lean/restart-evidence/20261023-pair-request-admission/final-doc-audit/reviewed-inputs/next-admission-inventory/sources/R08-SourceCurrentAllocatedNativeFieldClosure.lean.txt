import MicroCFTA.SourceCurrentAllocatedNativeCodeFields
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceEqualityNativeDemandFieldExecution
import MicroCFTA.SourceEqualityNativeDemandControl

/-!
# Allocated equality fields follow actual checked continuations

Each new edge annotation has a successful load in the current operation
cache. Actual checked allocation derives that load before child code exists.
Constructor instructions retain these loads through their actual heap effects.
The native input plan retains its explicit range and completion checks.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeFieldClosure
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConjunctionEquality (FieldAvailable)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "Heap" => SourceCurrentConjunctionEquality.Fields
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Existing successful loads imply the older normalized-field invariant. -/
theorem normalized_heap (operations : Operations) (state : InternedConstructorTemplates.State Symbol Guard)
    (heap : Heap operations state) : SourceEqualityNativeDemandFieldHeap.Heap state := by
  intro key edge present
  exact (heap key edge present).1

/-- A continuation retains its static annotations and the actual original rows of a demanded body. -/
def Fields : Control Output → CheckedState width → Prop
  | .code code, state => CodeFields state.operations code
  | .edgeBody request next, state => EdgeReady state.native.machine request ∧ ∀ value, CodeFields state.operations (next value)

/-- Actual original row residency derives the operation-cache field check. -/
theorem operation_fields (control : Control Output) (state : CheckedState width)
    (heap : Heap state.operations state.native.machine.heap) (fields : Fields control state) :
    SourceEqualityNativeDemandOperations.Fields control := by
  cases control with
  | code => trivial
  | edgeBody request next =>
      exact SourceEqualityNativeDemandFieldHeap.body_fields request next state
        (normalized_heap state.operations state.native.machine.heap heap) fields.1

private theorem sentinel_fields (operations : Operations) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fields : ∀ value, CodeFields operations (next value)) :
    CodeFields (SourceEqualityMkEdgeAllocation.emptyField operations)
      ((SourceEqualityNativeCheckedCode.sentinel request.left).bind next) := by
  have actual := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) operations valid
  apply SourceCurrentAllocatedNativeCodeFields.fields_bind _ _ _
    (SourceCurrentAllocatedNativeCodeFields.sentinel_fields _ request.left actual.2.2)
  intro value
  exact SourceCurrentAllocatedNativeCodeFields.fields_grows operations _ (next value) (fields value) actual.2.1

/-- Every actual yielded prefix derives its new annotation from the actual conjunction result. -/
theorem body_fields (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state after : CheckedState width) (rest : Control Output)
    (heap : Heap state.operations state.native.machine.heap) (ready : EdgeReady state.native.machine request)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations) (fields : ∀ value, CodeFields state.operations (next value))
    (one : body request next state = .yielded rest after) : Fields rest after := by
  by_cases arity : request.left.children.length = request.right.children.length
  · have matched : ¬request.left.children.length ≠ request.right.children.length := by omega
    simp only [SourceEqualityNativeDemand.body, ite_eq_right matched] at one
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints with
    | error message => simp only [firstLoaded] at one; cases one
    | ok first =>
        cases first with
        | none => simp only [firstLoaded] at one; cases one
        | some first =>
            simp only [firstLoaded] at one
            cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints with
            | error message => simp only [secondLoaded] at one; cases one
            | ok second =>
                cases second with
                | none => simp only [secondLoaded] at one; cases one
                | some second =>
                    simp only [secondLoaded] at one
                    have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints
                      (heap _ _ ready.2.1).1 first firstLoaded).1
                    have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints
                      (heap _ _ ready.2.2).1 second secondLoaded).1
                    obtain ⟨branch, done, _, afterValid, growth, allocated⟩ :=
                      SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le first second
                        request.left.children.length request.right.children.length state.operations valid firstReady secondReady
                    have later : ∀ value, CodeFields
                        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
                          request.left.children.length request.right.children.length state.operations).2 (next value) :=
                      fun value => SourceCurrentAllocatedNativeCodeFields.fields_grows state.operations _ (next value) (fields value) growth
                    cases branch with
                    | mismatch | rejected =>
                      simp only [done] at one
                      cases one
                      exact sentinel_fields _ request next afterValid later
                    | ready combined =>
                      simp only [done] at one
                      have receipt := allocated combined rfl
                      have available := SourceCurrentConjunctionFieldAllocation.of_receipt
                        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
                          request.left.children.length request.right.children.length state.operations).2
                        (SourceEqualityConjoinAllocation.readback combined) receipt.2.1 combined.stored receipt.1 receipt.2.2
                      cases one
                      exact SourceCurrentAllocatedNativeCodeFields.fields_bind _ _ _
                        (SourceCurrentAllocatedNativeCodeFields.children_fields _ _ _ _ _ available) later
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left arity, sentinel] at one
    cases one
    exact sentinel_fields state.operations request next valid fields

/-- Resident loaded fields construct the next checked body without a missing-field premise. -/
theorem body_complete (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Output) (state : CheckedState width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (heap : Heap state.operations state.native.machine.heap) (ready : EdgeReady state.native.machine request)
    (fields : ∀ value, CodeFields state.operations (next value)) :
    ∃ code after, body request next state = .yielded (.code code) {state with operations := after} ∧
      SourceEqualityConstraintMemoAllocation.Valid after ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after ∧
      Heap after state.native.machine.heap ∧ Fields (.code code) {state with operations := after} := by
  have left := heap _ _ ready.2.1
  have right := heap _ _ ready.2.2
  obtain ⟨first, firstLoaded⟩ := left.2
  obtain ⟨second, secondLoaded⟩ := right.2
  obtain ⟨code, after, actual⟩ := SourceEqualityNativeDemand.body_complete request next state valid
    left.1 right.1 first second firstLoaded secondLoaded
  have effects := SourceEqualityNativeDemandOperations.body_operations request next state valid left.1 right.1
  have current : SourceEqualityConstraintMemoAllocation.Valid after ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations after := by
    simpa only [actual, Outcome.state] using effects
  exact ⟨code, after, actual, current.1, current.2,
    SourceCurrentConjunctionEquality.Fields.grows heap current.2,
    body_fields request next state {state with operations := after} (.code code) heap ready valid fields actual⟩

/-- Every outcome retains successful field loads; yielded continuations retain their current checks. -/
def OutcomeFields (outcome : Outcome width Output) : Prop :=
  Heap outcome.state.operations outcome.state.native.machine.heap ∧ match outcome with
    | .yielded control state => Fields control state
    | _ => True

private theorem lift_native (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native = outcome.state := by cases outcome <;> rfl

/-- Actual source instructions retain field loads in the returned operation cache. -/
theorem step_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (control : Control Output) (state : CheckedState width)
    (valid : SourceEqualityNativeDemandValidity.StateValid holds state) (heap : Heap state.operations state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandValidity.Inputs holds control state) (fields : Fields control state) :
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
          have chosenValid := SourceEqualityNativeDemandProvenance.lookupEdge_valid state.native valid.native request inputs.1 inputs.2
          cases selected : lookupEdge width request state.native with
          | mk handle chosen =>
              have chosenMachine : chosen.machine = state.native.machine := by
                simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request state.native
              simp only [selected] at chosenValid
              have currentValid := SourceEqualityNativeDemandProvenance.demandEdge_valid chosen chosenValid handle
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

end MicroCFTA.SourceCurrentAllocatedNativeFieldClosure
