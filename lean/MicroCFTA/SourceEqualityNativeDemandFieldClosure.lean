import MicroCFTA.SourceEqualityNativeDemandCodeFields

/-!
# Normalized fields follow actual checked continuations

Compiled code checks new work annotations. A demanded edge body retains its
actual resident original request. These current facts derive normalized
fields and preserve them through every actual step outcome.
-/
namespace MicroCFTA.SourceEqualityNativeDemandFieldClosure
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandFieldHeap (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
local notation "CodeFields" => SourceEqualityNativeDemandCodeFields.Fields

/-- A continuation retains its static annotations and the actual original rows of a demanded body. -/
def Fields : Control Output → CheckedState width → Prop
  | .code code, _ => CodeFields code
  | .edgeBody request next, state => EdgeReady state.native.machine request ∧ ∀ value, CodeFields (next value)

/-- Actual original row residency derives the operation-cache field check. -/
theorem operation_fields (control : Control Output) (state : CheckedState width)
    (heap : Heap state.native.machine.heap) (fields : Fields control state) :
    SourceEqualityNativeDemandOperations.Fields control := by
  cases control with
  | code => trivial
  | edgeBody request next => exact SourceEqualityNativeDemandFieldHeap.body_fields request next state heap fields.1

private theorem sentinel_fields (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (fields : ∀ value, CodeFields (next value)) :
    CodeFields ((SourceEqualityNativeCheckedCode.sentinel request.left).bind next) :=
  SourceEqualityNativeDemandCodeFields.fields_bind _ _ (SourceEqualityNativeDemandCodeFields.sentinel_fields _) fields

/-- Every actual yielded prefix derives its new annotation from the actual conjunction result. -/
theorem body_fields (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state after : CheckedState width) (rest : Control Output)
    (heap : Heap state.native.machine.heap) (ready : EdgeReady state.native.machine request)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations) (fields : ∀ value, CodeFields (next value))
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
                    split at one
                    · cases one
                    · cases one
                      exact sentinel_fields request next fields
                    · cases one
                      exact sentinel_fields request next fields
                    · rename_i combined checked
                      cases one
                      apply SourceEqualityNativeDemandCodeFields.fields_bind _ _ _ fields
                      apply SourceEqualityNativeDemandCodeFields.children_fields
                      exact SourceEqualityNativeDemandFieldHeap.ready_cached request state heap ready valid
                        first second combined arity firstLoaded secondLoaded checked
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left arity, sentinel] at one
    cases one
    exact sentinel_fields request next fields

/-- Every actual outcome has a normalized heap; a yielded continuation retains its current field facts. -/
def OutcomeFields (outcome : Outcome width Output) : Prop :=
  Heap outcome.state.native.machine.heap ∧ match outcome with
    | .yielded control state => Fields control state
    | _ => True

private theorem lift_native (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native = outcome.state := by cases outcome <;> rfl

/-- Actual current source inputs retain normalized fields through all native instructions. -/
theorem step_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (control : Control Output) (state : CheckedState width)
    (valid : SourceEqualityNativeDemandValidity.StateValid holds state) (heap : Heap state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandValidity.Inputs holds control state) (fields : Fields control state) :
    OutcomeFields (step control state) := by
  cases control with
  | edgeBody request next =>
      have retained : Heap (body request next state).state.native.machine.heap := by
        rw [SourceEqualityNativeDemandOperations.body_native]
        exact heap
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
          exact ⟨SourceEqualityNativeDemandFieldHeap.work_heap job state.native.machine.heap heap fields.1, fields.2 _⟩
      | enter domain left right first second next => exact ⟨heap, fields _⟩
      | optionalBinder pair value next =>
          have retained := SourceEqualityNativeDemandFieldHeap.optionalBinder_heap pair value state.native.machine.heap
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
          have retained : Heap (step (.code (.node request next)) state).state.native.machine.heap := by
            change Heap (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) state.native)).state.native.machine.heap
            rw [lift_native, physical]
            exact heap
          refine ⟨retained, ?_⟩
          cases selected : lookupNode width request state.native with
          | mk selection chosen =>
              cases selection with
              | direct actual =>
                  simpa only [step, SourceRecursiveIntersectionNative.step, selected, lift, Fields] using
                    SourceEqualityNativeDemandCodeFields.fields_bind _ _
                      (SourceEqualityNativeDemandCodeFields.compileNode_fields actual) fields
              | memoized handle =>
                  cases demanded : demandNode handle chosen with
                  | mk observation current =>
                      cases observation with
                      | absent | busy => simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift]
                      | ready result =>
                          simpa only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, Fields] using fields result
                      | evaluate actual =>
                          simpa only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, Fields] using
                            SourceEqualityNativeDemandCodeFields.fields_bind _ (fun value => .finishNode handle value (next value))
                              (SourceEqualityNativeDemandCodeFields.compileNode_fields actual) (fun value => fields value)
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
                  have retained : Heap current.machine.heap := by rw [currentMachine]; exact heap
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

end MicroCFTA.SourceEqualityNativeDemandFieldClosure
