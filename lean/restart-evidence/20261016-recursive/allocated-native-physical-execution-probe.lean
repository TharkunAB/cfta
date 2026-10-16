import MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution

open MicroCFTA
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks SourceRecursiveIntersectionKernel
open SourceEqualityNativeDemand SourceCurrentAllocatedNativePhysicalExecution
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

#print axioms SourceCurrentAllocatedNativePhysicalExecution.work_checked
#print axioms SourceCurrentAllocatedNativePhysicalExecution.node_step_valid
#print axioms SourceCurrentAllocatedNativePhysicalExecution.edge_step_valid
#print axioms SourceCurrentAllocatedNativePhysicalExecution.step_valid
#print axioms SourceCurrentAllocatedNativePhysicalExecution.step_extension
#print axioms SourceCurrentAllocatedNativePhysicalExecution.inputs_heap
#print axioms SourceCurrentAllocatedNativePhysicalExecution.code_inputs
#print axioms SourceCurrentAllocatedNativePhysicalExecution.through_heap
#print axioms SourceCurrentAllocatedNativePhysicalExecution.step_invariants
#print axioms SourceCurrentAllocatedNativePhysicalExecution.execute_invariants

#print axioms SourceCurrentAllocatedNativePhysicalExecution.node_busy_impossible
#print axioms SourceCurrentAllocatedNativePhysicalExecution.edge_busy_impossible

#check SourceCurrentAllocatedNativePhysicalExecution.code_inputs
#check SourceCurrentAllocatedNativePhysicalExecution.execute_invariants

/-- A direct request has no packed-key range obligation. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : Checked width) (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.native.machine request)
    (none : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none) :
    SourceCurrentAllocatedNativePhysicalCache.Valid
      (step (.code (.node request .pure)) state).state.native := by
  apply node_step_valid request .pure state valid ready
  intro key present
  rw [none] at present
  cases present

/-- A running node stores a resident value without a semantic result receipt. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : Checked width) (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : state.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (available : Available state.native.machine.heap value) :
    SourceCurrentAllocatedNativePhysicalCache.Valid
      (step (.code (.finishNode handle value (.pure value))) state).state.native := by
  exact step_valid _ state valid ⟨request, running, available⟩

/-- A running edge stores a resident row without a semantic result receipt. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : Checked width) (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (running : state.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (resident : EdgeResident state.native.machine.heap value) :
    SourceCurrentAllocatedNativePhysicalCache.Valid
      (step (.code (.finishEdge handle value (.pure value))) state).state.native := by
  exact step_valid _ state valid ⟨request, running, resident⟩

/-- Even a blocked or erroneous checked body retains physical native validity. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : Checked width) (valid : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (request : EdgeRequest Symbol Guard) :
    SourceCurrentAllocatedNativePhysicalCache.Valid
      (step (.edgeBody request .pure) state).state.native :=
  step_valid _ state valid trivial

/-- The source certificate bridge is independent of a language interpretation or schedule rank. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (code : Code Symbol Guard A) (state : Checked width)
    (operands : SourceCurrentAllocatedNativeCodeProgress.Operands code state.native.machine)
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width (.code code)) :
    Inputs (.code code) state := code_inputs code state operands words

/-- Every finite actual outcome supplies the heap checks used by semantic and cost preservation. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (state : Checked width)
    (checks : InputsThrough fuel control state) :
    SourceEqualityNativeDemandHeap.InputsThrough fuel control state := through_heap fuel control state checks
