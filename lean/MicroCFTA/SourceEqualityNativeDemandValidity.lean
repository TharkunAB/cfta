import MicroCFTA.SourceEqualityNativeDemandCellValidity
import MicroCFTA.SourceEqualityNativeDemandHeap
import MicroCFTA.SourceRecursiveIntersectionKernelCalls

/-!
# Current checks for checked native execution

Current constructor arguments derive physical validity and growth. Original
request inputs and word bounds derive memo validity. Completion checks use
the actual running cell and its checked body receipt. They do not assume a
future valid state. Derivation of these checks from compiled continuations
remains a separate obligation.
-/
namespace MicroCFTA.SourceEqualityNativeDemandValidity
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- Current work operands derive source validity and both physical histories. -/
theorem work_checked [DecidableEq (EdgeKey Symbol Guard)]
    (job : Work Symbol Guard X) (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) (inputs : WorkInputs machine.heap job) :
    SourceRecursiveIntersectionKernel.Valid {machine with heap := (run job machine.heap).2} ∧
      Extension machine {machine with heap := (run job machine.heap).2} := by
  cases inputs with
  | pure value => exact ⟨valid, .refl _⟩
  | edge symbol guard values available =>
      have checked := SourceRecursiveIntersectionKernel.work_checked machine valid _ _
        (InternedNestedFacts.edge_verified symbol guard values machine.heap valid.1 available)
      exact ⟨checked.valid, checked.extension⟩
  | node edges resident =>
      have checked := SourceRecursiveIntersectionKernel.work_checked machine valid _ _
        (InternedNestedFacts.node_verified edges machine.heap valid.1 resident)
      exact ⟨checked.valid, checked.extension⟩
  | union values available =>
      have checked := SourceRecursiveIntersectionKernel.work_checked machine valid _ _
        (InternedNestedFacts.union_verified values machine.heap valid.1 available)
      exact ⟨checked.valid, checked.extension⟩

/-- Each check refers only to the current instruction, current inputs, and current running cell. -/
def Inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) : Control Output → CheckedState width → Prop
  | .code (.work job _), state => WorkInputs state.native.machine.heap job
  | .code (.enter domain left right _ _ _), state =>
      Domain state.native.machine domain ∧ Available state.native.machine.heap left ∧ Available state.native.machine.heap right
  | .code (.optionalBinder _ value _), state => Available state.native.machine.heap value
  | .code (.node request _), state => NodeReady state.native.machine request ∧
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right
  | .code (.edge request _), state => EdgeReady state.native.machine request ∧
      SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right
  | .code (.finishNode handle value _), state => ∃ request,
      state.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      NodeProduced (width := width) holds state.native.machine request value
  | .code (.finishEdge handle value _), state => ∃ request,
      state.native.edges.cells handle = some ⟨request, .evaluating⟩ ∧
      EdgeProduced (width := width) holds state.native.machine request value
  | _, _ => True

private theorem lift_native (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native = outcome.state := by cases outcome <;> rfl

/-- Actual node publication and demand preserve checked cells from current inputs and word bounds. -/
theorem node_step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard Output) (state : CheckedState width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native)
    (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) :
    SourceEqualityNativeDemandProvenance.Valid holds (step (.code (.node request next)) state).state.native := by
  have chosen := SourceEqualityNativeDemandProvenance.lookupNode_valid state.native valid request ready safe
  cases selected : lookupNode width request state.native with
  | mk selection current =>
      simp only [selected] at chosen
      cases selection with
      | direct actual => simpa only [step, SourceRecursiveIntersectionNative.step, selected, lift, Outcome.state] using chosen
      | memoized handle =>
          have checked := SourceEqualityNativeDemandProvenance.demandNode_valid current chosen handle
          cases demanded : demandNode handle current with
          | mk observation after =>
              simp only [demanded] at checked
              cases observation <;>
                simpa only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, Outcome.state] using checked

/-- Actual edge publication and demand preserve checked cells from current original rows and word bounds. -/
theorem edge_step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Output) (state : CheckedState width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native)
    (ready : EdgeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) :
    SourceEqualityNativeDemandProvenance.Valid holds (step (.code (.edge request next)) state).state.native := by
  have chosen := SourceEqualityNativeDemandProvenance.lookupEdge_valid state.native valid request ready safe
  cases selected : lookupEdge width request state.native with
  | mk handle current =>
      simp only [selected] at chosen
      have checked := SourceEqualityNativeDemandProvenance.demandEdge_valid current chosen handle
      cases demanded : demandEdge handle current with
      | mk observation after =>
          simp only [demanded] at checked
          cases observation <;> simpa only [step, selected, demanded, Outcome.state] using checked

/-- Current checks derive checked native validity on every complete, failed, blocked, or yielded outcome. -/
theorem step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (control : Control Output) (state : CheckedState width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native) (inputs : Inputs holds control state) :
    SourceEqualityNativeDemandProvenance.Valid holds (step control state).state.native := by
  cases control with
  | edgeBody request next =>
      rw [step, SourceEqualityNativeDemandOperations.body_native]
      exact valid
  | code code =>
      cases code with
      | pure | fail | read => exact valid
      | work job next =>
          have checked := work_checked job state.native.machine valid.machine inputs
          exact SourceEqualityNativeDemandProvenance.advance_valid state.native valid _ checked.1 checked.2
      | enter domain left right first second next =>
          have checked := entered state.native.machine valid.machine domain inputs.1 left right inputs.2.1 inputs.2.2 first second
          exact SourceEqualityNativeDemandProvenance.advance_valid state.native valid _ checked.1 checked.2.1
      | optionalBinder pair body next =>
          have checked := construction_checked state.native.machine valid.machine _ Available
            (SourceRecursiveIntersectionMaybeMu.verified pair body state.native.machine.heap valid.machine.1 inputs)
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.native.machine.heap with
          | done value heap | pending key heap =>
              have physical := checked.valid
              have growth := checked.extension
              simp only [actual, construction, Result.state] at physical growth
              simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state] using
                SourceEqualityNativeDemandProvenance.advance_valid state.native valid _ physical growth
      | node request next => exact node_step_valid holds request next state valid inputs.1 inputs.2
      | edge request next => exact edge_step_valid holds request next state valid inputs.1 inputs.2
      | finishNode handle value next =>
          obtain ⟨request, running, produced⟩ := inputs
          exact SourceEqualityNativeDemandProvenance.finishNode_valid state.native valid handle request value running produced
      | finishEdge handle value next =>
          obtain ⟨request, running, produced⟩ := inputs
          exact SourceEqualityNativeDemandProvenance.finishEdge_valid state.native valid handle request value running produced

/-- Each actual checked instruction retains physical records, issued identities, and source domains. -/
theorem step_extension [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (control : Control Output) (state : CheckedState width)
    (valid : SourceRecursiveIntersectionKernel.Valid state.native.machine) (inputs : Inputs holds control state) :
    Extension state.native.machine (step control state).state.native.machine := by
  cases control with
  | edgeBody request next =>
      rw [step, SourceEqualityNativeDemandOperations.body_native]
      exact .refl _
  | code code =>
      cases code with
      | pure | fail | read | finishNode | finishEdge => exact .refl _
      | work job next => exact (work_checked job state.native.machine valid inputs).2
      | enter domain left right first second next =>
          exact (entered state.native.machine valid domain inputs.1 left right inputs.2.1 inputs.2.2 first second).2.1
      | optionalBinder pair value next =>
          have checked := construction_checked state.native.machine valid _ Available
            (SourceRecursiveIntersectionMaybeMu.verified pair value state.native.machine.heap valid.1 inputs)
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair value state.native.machine.heap with
          | done result heap | pending key heap =>
              have growth := checked.extension
              simpa only [actual, construction, Result.state, step, SourceRecursiveIntersectionNative.step,
                lift, Outcome.state, advance] using growth
      | node request next =>
          change Extension state.native.machine
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) state.native)).state.native.machine
          rw [lift_native, SourceRecursiveIntersectionNative.node_step_machine]
          exact .refl _
      | edge request next =>
          cases selected : lookupEdge width request state.native with
          | mk handle chosen =>
              have first : chosen.machine = state.native.machine := by
                simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request state.native
              cases demanded : demandEdge handle chosen with
              | mk observation current =>
                  have second : current.machine = chosen.machine := by
                    simpa only [demanded] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
                  have growth : Extension state.native.machine current.machine := by
                    rw [second, first]
                    exact .refl _
                  cases observation <;> simpa only [step, selected, demanded, Outcome.state] using growth

/-- Native current checks include every physical input check required by heap preservation. -/
theorem inputs_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (control : Control Output) (state : CheckedState width)
    (inputs : Inputs holds control state) : SourceEqualityNativeDemandHeap.Inputs control state := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact inputs | trivial

/-- The three current cache families retain their separate invariants. -/
structure StateValid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (state : CheckedState width) : Prop where
  native : SourceEqualityNativeDemandProvenance.Valid holds state.native
  heap : SourceEqualityRequiredCache.Ready state.native.machine.heap
  operations : SourceEqualityConstraintMemoAllocation.Valid state.operations

/-- Current native checks and normalized original fields suffice for one actual instruction. -/
theorem step_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (control : Control Output) (state : CheckedState width)
    (valid : StateValid holds state) (inputs : Inputs holds control state)
    (fields : SourceEqualityNativeDemandOperations.Fields control) :
    StateValid holds (step control state).state ∧
      Extension state.native.machine (step control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (step control state).state.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations (step control state).state.operations := by
  have native := step_valid holds control state valid.native inputs
  have growth := step_extension holds control state valid.native.machine inputs
  have heap := SourceEqualityNativeDemandHeap.step_keeps control state valid.heap (inputs_heap holds control state inputs)
  have operations := SourceEqualityNativeDemandOperations.step_operations control state valid.operations fields
  exact ⟨⟨native, heap.ready, operations.1⟩, growth, heap, operations.2⟩

/-- Checks follow only the controls and full states reached by the actual execution. -/
noncomputable def Through [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) : Nat → Control Output → CheckedState width → Prop
  | 0, control, state => Inputs holds control state ∧ SourceEqualityNativeDemandOperations.Fields control
  | fuel + 1, control, state =>
      Inputs holds control state ∧ SourceEqualityNativeDemandOperations.Fields control ∧
        match step control state with
        | .yielded next after => Through holds fuel next after
        | .done _ _ | .failed _ _ | .constraintError _ _ | .blocked _ _ _ => True

private theorem operations_trans {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : SourceEqualityConstraintMemoAllocation.Grows before middle)
    (second : SourceEqualityConstraintMemoAllocation.Grows middle after) :
    SourceEqualityConstraintMemoAllocation.Grows before after :=
  ⟨SourceEqualityConstraintAllocation.steps_trans first.constraints second.constraints,
    Cache.extends_trans first.combinations second.combinations, Cache.extends_trans first.descents second.descents⟩

/-- Reached current checks derive all cache invariants and histories on every finite outcome. -/
theorem execute_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : CheckedState width)
    (valid : StateValid holds state) (checks : Through holds fuel control state) :
    StateValid holds (execute fuel control state).state ∧
      Extension state.native.machine (execute fuel control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (execute fuel control state).state.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations (execute fuel control state).state.operations := by
  induction fuel generalizing control state with
  | zero => exact ⟨valid, .refl _, SourceEqualityRequiredCache.pure_keeps _ valid.heap,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  | succ fuel ih =>
      have one := step_invariants holds control state valid checks.1 checks.2.1
      cases observed : step control state with
      | yielded next after =>
          have current : StateValid holds after ∧ Extension state.native.machine after.native.machine ∧
              SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap ∧
              SourceEqualityConstraintMemoAllocation.Grows state.operations after.operations := by
            simpa only [observed, Outcome.state] using one
          have later := ih next after current.1 (by simpa only [Through, observed] using checks.2.2)
          simpa only [SourceEqualityNativeDemand.execute, observed] using And.intro later.1
            ⟨current.2.1.trans later.2.1, current.2.2.1.trans later.2.2.1,
              operations_trans current.2.2.2 later.2.2.2⟩
      | done | failed | constraintError | blocked =>
          simpa only [SourceEqualityNativeDemand.execute, observed, Outcome.state] using one

end MicroCFTA.SourceEqualityNativeDemandValidity
