import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.SourceCurrentAllocatedNativeCodeProgress
import MicroCFTA.SourceEqualityNativeDemandHeap
import MicroCFTA.SourceRecursiveIntersectionKernelCalls
import MicroCFTA.SourceRecursiveIntersectionNativeDemandProgress

/-!
# Physical invariants through actual checked execution

Current physical operands and word bounds preserve both native memo families.
A finish checks its actual running cell and the resident value to install.
The checks contain no language law or semantic completion receipt.
Finite execution retains every complete and incomplete observation.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedNativePhysicalCache
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
    : Control Output → CheckedState width → Prop
  | .code (.work job _), state => WorkInputs state.native.machine.heap job
  | .code (.enter domain left right _ _ _), state =>
      Domain state.native.machine domain ∧ Available state.native.machine.heap left ∧ Available state.native.machine.heap right
  | .code (.optionalBinder _ value _), state => Available state.native.machine.heap value
  | .code (.node request _), state => NodeReady state.native.machine request ∧
      ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
        SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right
  | .code (.edge request _), state => EdgeReady state.native.machine request ∧
      SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right
  | .code (.finishNode handle value _), state => ∃ request,
      state.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      Available state.native.machine.heap value
  | .code (.finishEdge handle value _), state => ∃ request,
      state.native.edges.cells handle = some ⟨request, .evaluating⟩ ∧
      InternedEdgeResidency.EdgeResident state.native.machine.heap value
  | _, _ => True

private theorem lift_native (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native = outcome.state := by cases outcome <;> rfl

/-- Actual node publication and demand preserve resident inputs and completed values. -/
theorem node_step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard Output) (state : CheckedState width)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (ready : NodeReady state.native.machine request)
    (safe : ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (step (.code (.node request next)) state).state.native := by
  have chosen : SourceCurrentAllocatedNativePhysicalCache.Valid (lookupNode width request state.native).2 := by
    cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
    | none => simpa only [lookupNode, key] using valid
    | some physical => exact SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid state.native valid request ready (safe physical key)
  cases selected : lookupNode width request state.native with
  | mk selection current =>
      simp only [selected] at chosen
      cases selection with
      | direct actual => simpa only [step, SourceRecursiveIntersectionNative.step, selected, lift, Outcome.state] using chosen
      | memoized handle =>
          have checked := SourceCurrentAllocatedNativePhysicalCache.demandNode_valid current chosen handle
          cases demanded : demandNode handle current with
          | mk observation after =>
              simp only [demanded] at checked
              cases observation <;>
                simpa only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, Outcome.state] using checked

/-- Actual edge publication and demand preserve original rows and resident completed results. -/
theorem edge_step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Output) (state : CheckedState width)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (ready : EdgeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (step (.code (.edge request next)) state).state.native := by
  have chosen := SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid state.native valid request ready safe
  cases selected : lookupEdge width request state.native with
  | mk handle current =>
      simp only [selected] at chosen
      have checked := SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid current chosen handle
      cases demanded : demandEdge handle current with
      | mk observation after =>
          simp only [demanded] at checked
          cases observation <;> simpa only [step, selected, demanded, Outcome.state] using checked

/-- Current physical checks preserve both memo families on every actual step outcome. -/
theorem step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : CheckedState width)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state.native) (inputs : Inputs control state) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (step control state).state.native := by
  cases control with
  | edgeBody request next =>
      rw [step, SourceEqualityNativeDemandOperations.body_native]
      exact valid
  | code code =>
      cases code with
      | pure | fail | read => exact valid
      | work job next =>
          have checked := work_checked job state.native.machine valid.machine inputs
          exact SourceCurrentAllocatedNativePhysicalCache.advance_valid state.native valid _ checked.1 checked.2
      | enter domain left right first second next =>
          have checked := entered state.native.machine valid.machine domain inputs.1 left right inputs.2.1 inputs.2.2 first second
          exact SourceCurrentAllocatedNativePhysicalCache.advance_valid state.native valid _ checked.1 checked.2.1
      | optionalBinder pair body next =>
          have checked := construction_checked state.native.machine valid.machine _ Available
            (SourceRecursiveIntersectionMaybeMu.verified pair body state.native.machine.heap valid.machine.1 inputs)
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.native.machine.heap with
          | done value heap | pending key heap =>
              have physical := checked.valid
              have growth := checked.extension
              simp only [actual, construction, Result.state] at physical growth
              simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state] using
                SourceCurrentAllocatedNativePhysicalCache.advance_valid state.native valid _ physical growth
      | node request next => exact node_step_valid request next state valid inputs.1 inputs.2
      | edge request next => exact edge_step_valid request next state valid inputs.1 inputs.2
      | finishNode handle value next =>
          obtain ⟨request, running, resident⟩ := inputs
          exact SourceCurrentAllocatedNativePhysicalCache.finishNode_valid state.native valid handle request value running resident
      | finishEdge handle value next =>
          obtain ⟨request, running, resident⟩ := inputs
          exact SourceCurrentAllocatedNativePhysicalCache.finishEdge_valid state.native valid handle request value running resident

/-- Each actual checked instruction retains physical records, issued identities, and source domains. -/
theorem step_extension [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : CheckedState width)
    (valid : SourceRecursiveIntersectionKernel.Valid state.native.machine) (inputs : Inputs control state) :
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
    (control : Control Output) (state : CheckedState width)
    (inputs : Inputs control state) : SourceEqualityNativeDemandHeap.Inputs control state := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact inputs | trivial

/-- Source operands and conditional word bounds derive the current physical check. -/
theorem code_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (code : Code Symbol Guard A) (state : CheckedState width)
    (operands : SourceCurrentAllocatedNativeCodeProgress.Operands code state.native.machine)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code code)) :
    Inputs (.code code) state := by
  cases code with
  | pure | fail | read => trivial
  | work | optionalBinder => exact operands.1
  | enter => exact ⟨operands.1, operands.2.1, operands.2.2.1⟩
  | node | edge => exact ⟨operands.1, words⟩
  | finishNode | finishEdge => cases operands

/-- Physical checks follow only the controls and states actually reached. -/
noncomputable def InputsThrough [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Control Output → CheckedState width → Prop
  | 0, control, state => Inputs control state
  | fuel + 1, control, state => Inputs control state ∧ match step control state with
      | .yielded next after => InputsThrough fuel next after
      | .done _ _ | .failed _ _ | .constraintError _ _ | .blocked _ _ _ => True

/-- The physical execution plan supplies the current heap checks used by cost and semantic preservation. -/
theorem through_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : CheckedState width)
    (inputs : InputsThrough fuel control state) :
    SourceEqualityNativeDemandHeap.InputsThrough fuel control state := by
  induction fuel generalizing control state with
  | zero => exact inputs_heap control state inputs
  | succ fuel ih =>
      refine ⟨inputs_heap control state inputs.1, ?_⟩
      cases actual : step control state with
      | yielded next after =>
          exact ih next after (by simpa only [InputsThrough, actual] using inputs.2)
      | done | failed | constraintError | blocked => trivial

/-- One checked step retains physical memo validity, domains, records, and identities. -/
theorem step_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : CheckedState width)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap) (inputs : Inputs control state) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (step control state).state.native ∧
      Extension state.native.machine (step control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (step control state).state.native.machine.heap :=
  ⟨step_valid control state valid inputs, step_extension control state valid.machine inputs,
    SourceEqualityNativeDemandHeap.step_keeps control state ready (inputs_heap control state inputs)⟩

/-- Every finite actual outcome retains the physical caches and both machine histories. -/
theorem execute_invariants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : CheckedState width)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (inputs : InputsThrough fuel control state) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (execute fuel control state).state.native ∧
      Extension state.native.machine (execute fuel control state).state.native.machine ∧
      SourceEqualityRequiredCache.Keeps state.native.machine.heap (execute fuel control state).state.native.machine.heap := by
  induction fuel generalizing control state with
  | zero => exact ⟨valid, .refl _, SourceEqualityRequiredCache.pure_keeps _ ready⟩
  | succ fuel ih =>
      have one := step_invariants control state valid ready inputs.1
      cases actual : step control state with
      | yielded next after =>
          have current : SourceCurrentAllocatedNativePhysicalCache.Valid after.native ∧
              Extension state.native.machine after.native.machine ∧
              SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap := by
            simpa only [actual, Outcome.state] using one
          have rest := ih next after current.1 current.2.2.ready
            (by simpa only [InputsThrough, actual] using inputs.2)
          simpa only [SourceEqualityNativeDemand.execute, actual] using And.intro rest.1
            ⟨current.2.1.trans rest.2.1, current.2.2.trans rest.2.2⟩
      | done | failed | constraintError | blocked =>
          simpa only [SourceEqualityNativeDemand.execute, actual, Outcome.state] using one

/-- A strict independent node bound excludes busy demand using only the physical captured request. -/
theorem node_busy_impossible [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (view : IntersectSchedule.View Symbol)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state) (active : SourceRecursiveIntersectionNative.ActiveAbove view holds bound state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (complete : IntersectSchedule.Completes view (SourceRecursiveIntersectionNative.nodeSemantic request)) (smaller : IntersectSchedule.requiredFuel view (SourceRecursiveIntersectionNative.nodeSemantic request) complete < bound)
    (handle : Nat) (lookup : lookupNode width request state = (.memoized handle, selected))
    (demand : demandNode handle selected = (.busy, current)) : False := by
  have selectedValid : SourceCurrentAllocatedNativePhysicalCache.Valid selected := by
    simpa only [lookup] using SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid state valid request ready safe
  have selectedActive : SourceRecursiveIntersectionNative.ActiveAbove view holds bound selected := by
    simpa only [lookup] using active.lookupNode view holds bound state request
  obtain ⟨key, requested, published, machine⟩ := SourceRecursiveIntersectionNative.lookupNode_memoized request state selected handle lookup
  have selectedReady : NodeReady selected.machine request := by simpa only [machine] using ready
  have flat : FlatMemoThunk.demand handle selected.nodes = (.busy, current.nodes) :=
    congrArg (fun actual => (actual.1, actual.2.nodes)) demand
  obtain ⟨original, stored, _⟩ := FlatMemoThunk.demand_busy_before handle selected.nodes current.nodes flat
  have same := SourceCurrentAllocatedNativePhysicalCache.node_request_exact selected selectedValid request selectedReady key
    ⟨requested, safe⟩ handle published ⟨original, .evaluating⟩ stored
  change original = request at same
  subst original
  obtain ⟨actualComplete, bounded⟩ := selectedActive.nodes handle request stored
  exact Nat.not_lt_of_ge bounded smaller

/-- A strict independent edge bound excludes busy demand using only the physical captured request. -/
theorem edge_busy_impossible [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (view : IntersectSchedule.View Symbol)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state) (active : SourceRecursiveIntersectionNative.ActiveAbove view holds bound state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (complete : IntersectSchedule.Completes view (SourceRecursiveIntersectionNative.edgeSemantic holds request)) (smaller : IntersectSchedule.requiredFuel view (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete < bound)
    (handle : Nat) (lookup : lookupEdge width request state = (handle, selected))
    (demand : demandEdge handle selected = (.busy, current)) : False := by
  have selectedValid : SourceCurrentAllocatedNativePhysicalCache.Valid selected := by
    simpa only [lookup] using SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid state valid request ready safe
  have selectedActive : SourceRecursiveIntersectionNative.ActiveAbove view holds bound selected := by
    simpa only [lookup] using active.lookupEdge view holds bound state request
  obtain ⟨published, machine⟩ := SourceRecursiveIntersectionNative.lookupEdge_selected request state selected handle lookup
  have selectedReady : EdgeReady selected.machine request := by simpa only [machine] using ready
  have flat : FlatMemoThunk.demand handle selected.edges = (.busy, current.edges) :=
    congrArg (fun actual => (actual.1, actual.2.edges)) demand
  obtain ⟨original, stored, _⟩ := FlatMemoThunk.demand_busy_before handle selected.edges current.edges flat
  have same := SourceCurrentAllocatedNativePhysicalCache.edge_request_exact selected selectedValid request selectedReady _
    ⟨rfl, safe⟩ handle published ⟨original, .evaluating⟩ stored
  change original = request at same
  subst original
  obtain ⟨actualComplete, bounded⟩ := selectedActive.edges handle request stored
  exact Nat.not_lt_of_ge bounded smaller


end MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution
