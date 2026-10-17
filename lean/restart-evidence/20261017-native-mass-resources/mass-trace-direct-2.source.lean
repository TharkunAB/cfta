import MicroCFTA.SourceRecursiveIntersectionWorkMass
import MicroCFTA.SourceCurrentAllocatedRecursiveMassBudget
import MicroCFTA.SourceCurrentAllocatedRecursiveAllocationTrace

/-!
# Numeric causal payload bounds through checked query prefixes

Every instruction retains a causal store bound. Literal constructor lists
need a width certificate. All other instructions use the physical checks
already recorded by the actual trace. A numeric recurrence then bounds the
store and both constructor supplies from the initial bound and step count.
The source compiler must still produce the width certificates for a whole
query. This theorem does not assume a future returned payload bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveMassTrace
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields OutcomeFields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => InternedValueMassHeap.Stored
local notation "PhysicalInputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width bound fuel : Nat} {A : Type}

/-- Hash-joined row lists use the square of the common payload bound. -/
def listLimit (bound : Nat) : Nat := bound * bound

/-- One numeric step covers a literal constructor or complete optional binder. -/
def ceiling (bound : Nat) : Nat :=
  max (InternedFreshOrdinaryResultMass.inflate (listLimit bound) bound)
    (SourceCurrentAllocatedRecursiveMassBudget.ceiling bound)

/-- A step cannot decrease the causal store bound. -/
theorem ceiling_ge (bound : Nat) : bound ≤ ceiling bound :=
  Nat.le_trans (InternedFreshOrdinaryResultMass.inflate_ge _ _) (Nat.le_max_left _ _)

/-- One numeric charge covers both constructor supplies at any instruction. -/
def charge (bound : Nat) : Nat := SourceCurrentAllocatedRecursiveMassBudget.charge bound + 1

/-- Only literal Work instructions need an additional list-width certificate. -/
def Inputs (bound : Nat) (control : Control A) (before : Checked width) : Prop :=
  match control with
  | .code (.work job _) => SourceRecursiveIntersectionWorkMass.Inputs (listLimit bound) before.native.machine.heap job
  | _ => True

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual stopping outcome retains the numeric store and allocation bounds. -/
theorem step_bound (control : Control A) (before : Checked width)
    (good : Good before) (physical : PhysicalInputs control before)
    (stored : Stored bound before.native.machine.heap) (inputs : Inputs bound control before) :
    Stored (ceiling bound) (step control before).state.native.machine.heap ∧
      (step control before).state.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + charge bound ∧
      (step control before).state.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + charge bound := by
  have unchanged (same : (step control before).state.native.machine.heap = before.native.machine.heap) :
      Stored (ceiling bound) (step control before).state.native.machine.heap ∧
        (step control before).state.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + charge bound ∧
        (step control before).state.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + charge bound := by
    rw [same]
    exact ⟨stored.mono (ceiling_ge bound), Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  cases control with
  | edgeBody request next =>
      apply unchanged
      simp only [step, SourceEqualityNativeDemandOperations.body_native]
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact unchanged rfl
      | work job next =>
          have actual := SourceRecursiveIntersectionWorkMass.run_bound stored inputs
          change Stored (ceiling bound) (run job before.native.machine.heap).2 ∧
            (run job before.native.machine.heap).2.nodes.next ≤ before.native.machine.heap.nodes.next + charge bound ∧
            (run job before.native.machine.heap).2.edges.next ≤ before.native.machine.heap.edges.next + charge bound
          have paid : 1 ≤ charge bound := by unfold charge; omega
          exact ⟨actual.1.mono (Nat.le_max_left _ _), by omega, by omega⟩
      | optionalBinder key body next =>
          have actual := SourceCurrentAllocatedRecursiveMassBudget.stored_bound key body before.native.machine.heap bound
            good.native.machine.1 stored physical
          have counters := SourceCurrentAllocatedRecursiveMassBudget.allocation_bound key body before.native.machine.heap bound
            good.native.machine.1 stored physical
          have same : (step (.code (.optionalBinder key body next)) before).state.native.machine.heap =
              (SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap).state := by
            cases done : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap <;>
              simp only [step, SourceRecursiveIntersectionNative.step, done, lift, Outcome.state,
                InternedNestedConstruction.Outcome.state, advance]
          rw [same]
          exact ⟨actual.1.mono (Nat.le_max_right _ _), by unfold charge; omega, by unfold charge; omega⟩
      | node request next =>
          apply unchanged
          change (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
            SourceEqualityPCSNativeEdge.conjoin (.node request next) before.native)).state.native.machine.heap = _
          rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
      | edge request next => exact unchanged (SourceEqualityNativeDemandHeap.step_edge_heap request next before)

/-- Iterate the numeric ceiling without inspecting any future state or instruction. -/
def massAfter : Nat → Nat → Nat
  | 0, bound => bound
  | count + 1, bound => massAfter count (ceiling bound)

/-- Accumulate one numeric charge for each checked instruction. -/
def credit : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, bound => charge bound + credit count (ceiling bound)

/-- Width certificates follow the actual yielded controls and numeric recurrence. -/
noncomputable def InputsThrough : Nat → Nat → Control A → Checked width → Prop
  | 0, _, _, _ => True
  | count + 1, bound, control, before =>
      Inputs bound control before ∧ match step control before with
      | .yielded next after => InputsThrough count (ceiling bound) next after
      | _ => True

/-- Certified literal widths turn an actual prefix into initial numeric store and supply bounds. -/
theorem prefix_bound {control next : Control A} {before after : Checked width}
    (actual : Trace fuel control before next after) (good : Good before) (fields : Fields control before)
    (stored : Stored bound before.native.machine.heap) (inputs : InputsThrough fuel bound control before) :
    Good after ∧ Fields next after ∧ Stored (massAfter fuel bound) after.native.machine.heap ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit fuel bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit fuel bound := by
  induction actual generalizing bound with
  | refl => exact ⟨good, fields, stored, by simp only [credit, Nat.add_zero, Nat.le_refl],
      by simp only [credit, Nat.add_zero, Nat.le_refl]⟩
  | cons control before middle current next after count physical one rest ih =>
      have own := step_bound control before good physical stored inputs.1
      have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good physical fields
      have reached : Good current := by simpa only [one, Outcome.state] using effects.1
      have remaining : Fields middle current := by simpa only [one, OutcomeFields] using effects.2.2.2.2.2
      have currentStore : Stored (ceiling bound) current.native.machine.heap := by simpa only [one, Outcome.state] using own.1
      have tail : InputsThrough count (ceiling bound) middle current := by
        simpa only [InputsThrough, one] using inputs.2
      obtain ⟨lastGood, lastFields, lastStore, nodes, edges⟩ := ih reached remaining currentStore tail
      have nodeStep : current.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + charge bound := by
        simpa only [one, Outcome.state] using own.2.1
      have edgeStep : current.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + charge bound := by
        simpa only [one, Outcome.state] using own.2.2
      exact ⟨lastGood, lastFields, lastStore, by simp only [credit]; omega, by simp only [credit]; omega⟩

end MicroCFTA.SourceCurrentAllocatedRecursiveMassTrace
