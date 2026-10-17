import MicroCFTA.SourceCurrentAllocatedRecursiveOptionalBudget
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

/-!
# Allocation charges through full recursive checked prefixes

Literal Work requests charge their actual cache observations. Optional Mu
instructions charge their full initial body syntax budget. The proof covers
all checked instructions and both native memo families. It does not restrict
operands to ordinary trees. Prefix charges depend on the executed prefix.
A separate source compiler must bound them from the initial root inputs.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveAllocationTrace
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields OutcomeFields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (observe nodeRequests edgeRequests)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width : Nat} {A : Type}

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Each current instruction has a separate node and edge allocation charge. -/
noncomputable def stepCharges (control : Control A) (before : Checked width) : Nat × Nat :=
  match control with
  | .code (.work job _) =>
      let requests := observe job before.native.machine.heap
      (nodeRequests requests, edgeRequests requests)
  | .code (.optionalBinder key body _) =>
      (SourceCurrentAllocatedRecursiveOptionalBudget.nodeBudget key body,
        SourceCurrentAllocatedRecursiveOptionalBudget.edgeBudget key body)
  | _ => (0, 0)

/-- Accumulate charges from literal instructions and their actual returned states. -/
noncomputable def chargesThrough : Nat → Control A → Checked width → Nat × Nat
  | 0, _, _ => (0, 0)
  | fuel + 1, control, before =>
      let own := stepCharges control before
      match step control before with
      | .yielded next after =>
          let rest := chargesThrough fuel next after
          (own.1 + rest.1, own.2 + rest.2)
      | _ => own

/-- Every actual step outcome fits its current charge, including optional-binder failure. -/
theorem step_bound (control : Control A) (before : Checked width)
    (good : Good before) (inputs : Inputs control before) :
    (step control before).state.native.machine.heap.nodes.next ≤
        before.native.machine.heap.nodes.next + (stepCharges control before).1 ∧
      (step control before).state.native.machine.heap.edges.next ≤
        before.native.machine.heap.edges.next + (stepCharges control before).2 := by
  cases control with
  | edgeBody request next =>
      have same := SourceEqualityNativeDemandOperations.body_native request next before
      simp only [stepCharges, step]
      rw [same]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge =>
          exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      | work job next =>
          change (run job before.native.machine.heap).2.nodes.next ≤
              before.native.machine.heap.nodes.next + nodeRequests (observe job before.native.machine.heap) ∧
            (run job before.native.machine.heap).2.edges.next ≤
              before.native.machine.heap.edges.next + edgeRequests (observe job before.native.machine.heap)
          exact SourceCurrentAllocatedFiniteOrdinaryReservations.run_next_le job before.native.machine.heap
      | optionalBinder key body next =>
          exact SourceCurrentAllocatedRecursiveOptionalBudget.checked_bound key body next before
            good.native.machine.1 inputs
      | node request next =>
          have same : (step (.code (.node request next)) before).state.native.machine.heap =
              before.native.machine.heap := by
            change (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) before.native)).state.native.machine.heap = _
            rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          simp only [stepCharges, Nat.add_zero]
          rw [same]
          exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Every finite physical prefix retains initial validity and fits its accumulated charges. -/
theorem prefix_bound {fuel : Nat} {control next : Control A} {before after : Checked width}
    (actual : Trace fuel control before next after) (good : Good before) (fields : Fields control before) :
    Good after ∧ Fields next after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + (chargesThrough fuel control before).1 ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + (chargesThrough fuel control before).2 := by
  induction actual with
  | refl => exact ⟨good, fields, Nat.le_refl _, Nat.le_refl _⟩
  | cons control before middle current next after count inputs one rest ih =>
      have own := step_bound control before good inputs
      have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good inputs fields
      have reached : Good current := by simpa only [one, Outcome.state] using effects.1
      have remaining : Fields middle current := by
        simpa only [one, OutcomeFields] using effects.2.2.2.2.2
      obtain ⟨lastGood, lastFields, nodes, edges⟩ := ih reached remaining
      have counted : current.native.machine.heap.nodes.next ≤
          before.native.machine.heap.nodes.next + (stepCharges control before).1 ∧
          current.native.machine.heap.edges.next ≤
          before.native.machine.heap.edges.next + (stepCharges control before).2 := by
        simpa only [one, Outcome.state] using own
      refine ⟨lastGood, lastFields, ?_, ?_⟩ <;> simp only [chargesThrough, one] <;> omega

/-- Two literal prefixes add their charges at the exact common control and state. -/
theorem charges_append {first : Nat} {control middle : Control A} {before current : Checked width}
    (actual : Steps first control before middle current) (second : Nat) :
    (chargesThrough (first + second) control before).1 =
        (chargesThrough first control before).1 + (chargesThrough second middle current).1 ∧
      (chargesThrough (first + second) control before).2 =
        (chargesThrough first control before).2 + (chargesThrough second middle current).2 := by
  induction actual with
  | refl => simp [chargesThrough]
  | cons control before middle current next after count one rest ih =>
      simp only [Nat.succ_add, chargesThrough, one]
      exact ⟨by rw [ih.1]; omega, by rw [ih.2]; omega⟩

end MicroCFTA.SourceCurrentAllocatedRecursiveAllocationTrace
