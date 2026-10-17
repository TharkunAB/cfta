import MicroCFTA.SourceCurrentAllocatedRecursiveRequestStep
import MicroCFTA.SourceCurrentAllocatedNativePhysicalMass
import MicroCFTA.SourceRecursiveIntersectionWorkMass
import MicroCFTA.SourceCurrentAllocatedRecursiveMassBudget
import MicroCFTA.SourceCurrentAllocatedRecursiveMassTrace
import MicroCFTA.SourceRecursiveIntersectionCompileWidth
import MicroCFTA.SourceEqualityNativeCheckedWidth
import MicroCFTA.SourceEqualityNativeDemandBodyYield

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

section Step
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

end Step

/-- The tighter local bound is covered by the common numeric step schedule. -/
theorem nextBound_le_ceiling (control : Control A) (bound : Nat) :
    nextBound control bound ≤ SourceCurrentAllocatedRecursiveMassTrace.ceiling bound := by
  cases control with
  | edgeBody => exact SourceCurrentAllocatedRecursiveMassTrace.ceiling_ge bound
  | code code =>
    cases code with
    | work => exact Nat.le_max_left _ _
    | optionalBinder => exact Nat.le_max_right _ _
    | pure | fail | enter | read | node | edge | finishNode | finishEdge =>
      exact SourceCurrentAllocatedRecursiveMassTrace.ceiling_ge bound

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Each control carries the current code widths and its exact result continuation. -/
def ControlAt (control : Control A) (before : Checked width) (bound : Nat)
    (post : Machine Symbol Guard → A → Prop) : Prop :=
  match control with
  | .code code => SourceRecursiveIntersectionCodeMass.At code before.native.machine bound post
  | .edgeBody request next => EdgeReady before.native.machine request ∧
      ∀ value after larger, SourceRecursiveIntersectionKernel.Valid after →
        Extension before.native.machine after → bound ≤ larger → Stored larger after.heap →
        EdgeResident after.heap value → SourceRecursiveIntersectionCodeMass.At (next value) after larger post

/-- Increasing the current common bound retains the same control certificate. -/
theorem ControlAt.mono (control : Control A) (before : Checked width) {first last : Nat}
    (certificate : ControlAt control before first post) (increase : first ≤ last) :
    ControlAt control before last post := by
  cases control with
  | code code => exact SourceRecursiveIntersectionCodeMass.mono code before.native.machine certificate increase
  | edgeBody request next =>
    refine ⟨certificate.1, ?_⟩
    intro value after larger valid growth enough stored resident
    exact certificate.2 value after larger valid growth (Nat.le_trans increase enough) stored resident

/-- A current control certificate supplies the literal Work width check. -/
theorem inputs (control : Control A) (before : Checked width) (bound : Nat)
    (certificate : ControlAt control before bound post) :
    SourceCurrentAllocatedRecursiveMassTrace.Inputs bound control before := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact certificate.1 | trivial

variable [DecidableEq Symbol]

/-- Each actual yielded instruction retains the code certificate at the common next bound. -/
theorem yielded_at (control next : Control A) (before after : Checked width)
    (bound : Nat) (post : Machine Symbol Guard → A → Prop)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (physical : PhysicalInputs control before)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control before)
    (stored : Stored bound before.native.machine.heap)
    (certificate : ControlAt control before bound post)
    (one : SourceEqualityNativeDemand.step control before = .yielded next after) :
    ControlAt next after (SourceCurrentAllocatedRecursiveMassTrace.ceiling bound) post := by
  have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good physical fields
  have current : SourceCurrentAllocatedNativePhysicalCompletion.Good after := by
    simpa only [one, SourceEqualityNativeDemand.Outcome.state] using effects.1
  have growth : Extension before.native.machine after.native.machine := by
    simpa only [one, SourceEqualityNativeDemand.Outcome.state] using effects.2.1
  have currentStored : Stored (SourceCurrentAllocatedRecursiveMassTrace.ceiling bound) after.native.machine.heap := by
    have own := SourceCurrentAllocatedRecursiveMassTrace.step_bound control before good physical stored
      (inputs control before bound certificate)
    simpa only [one, SourceEqualityNativeDemand.Outcome.state] using own.1
  have increase := SourceCurrentAllocatedRecursiveMassTrace.ceiling_ge bound
  cases control with
  | edgeBody request continuation =>
    obtain ⟨body, pureBody, same⟩ := SourceEqualityNativeDemandBodyYield.yielded_unbind request continuation before after next one
    subst next
    have boundCode := SourceEqualityNativeCheckedWidth.body_bind_at request before after body continuation bound
      good.native.machine stored certificate.1 pureBody post certificate.2
    exact SourceRecursiveIntersectionCodeMass.mono _ _ boundCode.2 increase
  | code code =>
    cases code with
    | pure | fail => cases one
    | work job continuation =>
      obtain ⟨rfl, rfl⟩ := SourceEqualityNativeDemand.Outcome.yielded.inj one
      exact certificate.2 _ _ _ current.native.machine growth increase currentStored rfl
    | enter domain left right first second continuation =>
      obtain ⟨rfl, rfl⟩ := SourceEqualityNativeDemand.Outcome.yielded.inj one
      exact certificate _ current.native.machine growth increase currentStored
    | read name continuation =>
      obtain ⟨rfl, rfl⟩ := SourceEqualityNativeDemand.Outcome.yielded.inj one
      exact SourceRecursiveIntersectionCodeMass.mono _ _ certificate increase
    | optionalBinder key body continuation =>
      have checked := construction_checked before.native.machine good.native.machine _ Available
        (SourceRecursiveIntersectionMaybeMu.verified key body before.native.machine.heap good.native.machine.1 certificate.1)
      cases done : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
      | pending pending heap =>
        simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, done,
          SourceEqualityNativeDemand.lift] at one
        cases one
      | done value heap =>
        simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, done,
          SourceEqualityNativeDemand.lift] at one
        obtain ⟨rfl, rfl⟩ := SourceEqualityNativeDemand.Outcome.yielded.inj one
        have available := checked.result value {before.native.machine with heap := heap}
          (by simp only [done, construction])
        exact certificate.2 value _ _ current.native.machine growth increase currentStored available
    | node request continuation =>
      obtain ⟨machine, _, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.node_yielded request continuation before
        next after good.native certificate.1 physical.2 one
      rcases branches with ⟨rfl, sameBefore⟩ | ⟨value, rfl, available⟩ | ⟨handle, rfl, _⟩
      · subst after
        apply SourceRecursiveIntersectionCodeMass.bind _ _ before.native.machine _ good.native.machine currentStored _ post
          (SourceRecursiveIntersectionCompileWidth.compileNode request before.native.machine _ good.native.machine currentStored certificate.1)
        intro value final larger valid finalGrowth enough finalStored available
        exact certificate.2 value final larger valid finalGrowth (Nat.le_trans increase enough) finalStored available
      · exact certificate.2 value after.native.machine _ current.native.machine growth increase currentStored available
      · apply SourceRecursiveIntersectionCodeMass.bind _ _ after.native.machine _ current.native.machine currentStored _ post
          (SourceRecursiveIntersectionCompileWidth.compileNode request after.native.machine _ current.native.machine currentStored
            (by rw [machine]; exact certificate.1))
        intro value final larger valid finalGrowth enough finalStored available
        exact certificate.2 value final larger valid (growth.trans finalGrowth)
          (Nat.le_trans increase enough) finalStored available
    | edge request continuation =>
      obtain ⟨machine, _, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.edge_yielded request continuation before
        next after good.native certificate.1 physical.2 one
      rcases branches with ⟨value, rfl, resident⟩ | ⟨handle, rfl, _⟩
      · exact certificate.2 value after.native.machine _ current.native.machine growth increase currentStored resident
      · refine ⟨by rw [machine]; exact certificate.1, ?_⟩
        intro value final larger valid finalGrowth enough finalStored resident
        exact certificate.2 value final larger valid (growth.trans finalGrowth)
          (Nat.le_trans increase enough) finalStored resident
    | finishNode handle value continuation | finishEdge handle value continuation =>
      obtain ⟨rfl, rfl⟩ := SourceEqualityNativeDemand.Outcome.yielded.inj one
      exact SourceRecursiveIntersectionCodeMass.mono _ _ certificate increase

end MicroCFTA.SourceCurrentAllocatedNativeWidthStep
