import MicroCFTA.SourceCurrentAllocatedRecursiveRequestStep
import MicroCFTA.SourceCurrentAllocatedNativePhysicalMass
import MicroCFTA.SourceRecursiveIntersectionWorkMass
import MicroCFTA.SourceCurrentAllocatedRecursiveMassBudget

/-!
# Current numeric bounds through checked native instructions

Literal constructor Work uses its current square input limit. Optional Mu
uses its current payload mass bound. Other checked instructions retain the
constructor heap. Each bound follows the actual returned state.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeWidthStep
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Control" => SourceEqualityNativeDemand.Control
local notation "Stored" => InternedValueMassHeap.Stored
local notation "PhysicalValid" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "PhysicalInputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width bound : Nat} {A : Type}

/-- The current instruction determines the next common constructor mass bound. -/
def nextBound (control : Control A) (bound : Nat) : Nat :=
  match control with
  | .code (.work _ _) => InternedFreshOrdinaryResultMass.inflate (bound * bound) bound
  | .code (.optionalBinder _ _ _) => SourceCurrentAllocatedRecursiveMassBudget.ceiling bound
  | _ => bound

/-- Every instruction retains its preceding common bound. -/
theorem nextBound_ge (control : Control A) (bound : Nat) : bound ≤ nextBound control bound := by
  cases control with
  | edgeBody => exact Nat.le_refl _
  | code code =>
    cases code with
    | work => exact InternedFreshOrdinaryResultMass.inflate_ge _ _
    | optionalBinder => exact SourceCurrentAllocatedRecursiveMassBudget.ceiling_ge _
    | pure | fail | enter | read | node | edge | finishNode | finishEdge => exact Nat.le_refl _

private theorem lift_native (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (SourceEqualityNativeDemand.lift operations outcome).state.native = outcome.state := by
  cases outcome <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual current checks derive the next heap bound for every checked step outcome. -/
theorem step_heap (control : Control A) (before : Checked width)
    (valid : PhysicalValid before.native) (stored : Stored bound before.native.machine.heap)
    (inputs : PhysicalInputs control before)
    (work : match control with
      | .code (.work job _) => SourceRecursiveIntersectionWorkMass.Inputs (bound * bound) before.native.machine.heap job
      | _ => True) :
    Stored (nextBound control bound) (SourceEqualityNativeDemand.step control before).state.native.machine.heap := by
  cases control with
  | edgeBody request next =>
    rw [SourceEqualityNativeDemand.step, SourceEqualityNativeDemandOperations.body_native]
    exact stored
  | code code =>
    cases code with
    | pure | fail | enter | read | finishNode | finishEdge => exact stored
    | work job next => exact (SourceRecursiveIntersectionWorkMass.run_bound stored work).1
    | optionalBinder pair body next =>
      have checked := SourceCurrentAllocatedRecursiveMassBudget.stored_bound pair body before.native.machine.heap
        bound valid.machine.1 stored inputs
      cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
      | done value heap | pending key heap =>
        simpa only [nextBound, SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
          actual, SourceEqualityNativeDemand.lift, SourceEqualityNativeDemand.Outcome.state,
          SourceRecursiveIntersectionThunks.advance, InternedNestedConstruction.Outcome.state] using checked.1
    | node request next =>
      have same : (SourceEqualityNativeDemand.step (.code (.node request next)) before).state.native.machine =
          before.native.machine := by
        change (SourceEqualityNativeDemand.lift before.operations (SourceRecursiveIntersectionNative.step
          SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin (.node request next) before.native)).state.native.machine = _
        rw [lift_native, SourceRecursiveIntersectionNative.node_step_machine]
      change Stored bound _
      rw [same]
      exact stored
    | edge request next =>
      rw [SourceEqualityNativeDemandHeap.step_edge_heap]
      exact stored

end MicroCFTA.SourceCurrentAllocatedNativeWidthStep
