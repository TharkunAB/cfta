-- UNCOMPILED CANDIDATE. No proof credit.
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness

/-!
# Full operands at an actual native domain entry

A checked entry retains both complete operands at its actual later control.
The proof derives availability and growth from the same checked prefix.
It does not reconstruct an operand from a DomainKey.
-/
namespace MicroCFTA.SourceCurrentNativeEnterCommonOperand
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey

set_option autoImplicit false
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem checked_trace_extension
    {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after) (valid : Physical before.native) :
    Physical after.native ∧ Extension before.native.machine after.native.machine := by
  induction actual with
  | refl => exact ⟨valid, .refl _⟩
  | cons control state next current final result count inputs one tail ih =>
      have currentValid : Physical current.native := by
        simpa only [one, Outcome.state] using
          SourceCurrentAllocatedNativePhysicalExecution.step_valid control state valid inputs
      have currentExtension : Extension state.native.machine current.native.machine := by
        simpa only [one, Outcome.state] using
          SourceCurrentAllocatedNativePhysicalExecution.step_extension control state valid.machine inputs
      have later := ih currentValid
      exact ⟨later.1, currentExtension.trans later.2⟩

/-- The actual checked entry preserves both full operands and their complete record identity. -/
theorem enter_prefix_common_operands
    (domain : Interned DomainKey) (left right : Node) (first second : Nat)
    (next : Interned DomainKey → Code Symbol Guard A)
    (fuel : Nat) (before after : Checked width) (rest : Control A)
    (valid : Physical before.native)
    (actual : Trace (fuel + 1) (.code (.enter domain left right first second next)) before rest after) :
    let allocated := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
      domain.key left right first second
    let enteredState : Checked width :=
      {before with native := advance before.native {before.native.machine with domains := allocated.2}}
    step (.code (.enter domain left right first second next)) before =
      .yielded (.code (next allocated.1)) enteredState ∧
    Trace fuel (.code (next allocated.1)) enteredState rest after ∧
    enteredState.native.machine.heap = before.native.machine.heap ∧
    enteredState.native.machine.domains = allocated.2 ∧
    enteredState.operations = before.operations ∧
    Domain before.native.machine domain ∧
    Available before.native.machine.heap left ∧ Available before.native.machine.heap right ∧
    Available after.native.machine.heap left ∧ Available after.native.machine.heap right ∧
    Domain enteredState.native.machine allocated.1 ∧ Domain after.native.machine allocated.1 ∧
    allocated.1.key = SourceRecursiveIntersectionDomain.extend domain.key
      ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst)
      (SourceRecursiveIntersectionControl.pair first second) ∧
    Extension before.native.machine after.native.machine ∧
    (∀ (pattern : Node), (pattern = left ∨ pattern = right) → pattern.free = [] →
      ∀ (patternId : Nat), SourceRecursiveIntersectionControl.identity pattern = some patternId →
      ∀ (candidate : Node), Available after.native.machine.heap candidate → candidate.free = [] →
      SourceRecursiveIntersectionControl.identity candidate = some patternId →
      candidate = pattern ∧ height candidate = height pattern) := by
  let allocated := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
    domain.key left right first second
  let enteredState : Checked width :=
    {before with native := advance before.native {before.native.machine with domains := allocated.2}}
  have enterStep : step (.code (.enter domain left right first second next)) before =
      .yielded (.code (next allocated.1)) enteredState := rfl
  dsimp only
  cases actual with
  | cons control state resume current final result count inputs one tail =>
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans enterStep)
      have enteredValid : Physical enteredState.native := by
        simpa only [enterStep, Outcome.state] using
          SourceCurrentAllocatedNativePhysicalExecution.step_valid _ before valid inputs
      have later := checked_trace_extension tail enteredValid
      have allocatedFacts := SourceRecursiveIntersectionKernel.entered before.native.machine valid.machine
        domain inputs.1 left right inputs.2.1 inputs.2.2 first second
      have leftFinal : Available after.native.machine.heap left :=
        later.2.available left inputs.2.1
      have rightFinal : Available after.native.machine.heap right :=
        later.2.available right inputs.2.2
      refine ⟨enterStep, tail, rfl, rfl, rfl, inputs.1, inputs.2.1, inputs.2.2,
        leftFinal, rightFinal, allocatedFacts.2.2,
        allocatedFacts.2.2.grows allocated.1 later.2,
        SourceRecursiveIntersectionSchedule.entered_key before.native.machine.domains valid.machine.2
          domain.key left right first second,
        allocatedFacts.2.1.trans later.2, ?_⟩
      intro pattern side patternClosed patternId patternIdentity candidate candidateAvailable candidateClosed candidateIdentity
      have patternAvailable : Available after.native.machine.heap pattern := by
        rcases side with rfl | rfl
        · exact leftFinal
        · exact rightFinal
      have same := SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective
        after.native.machine.heap later.1.machine.1 pattern candidate patternAvailable candidateAvailable
        patternClosed candidateClosed patternId patternIdentity candidateIdentity
      exact ⟨same.symm, congrArg height same.symm⟩

end MicroCFTA.SourceCurrentNativeEnterCommonOperand

#print axioms MicroCFTA.SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
#check MicroCFTA.SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
