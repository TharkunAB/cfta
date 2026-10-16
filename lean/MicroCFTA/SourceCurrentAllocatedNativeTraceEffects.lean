import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceCurrentAllocatedNativeCosts
import MicroCFTA.SourceCurrentAllocatedNativeEffects

/-!
# Conjunction readiness from actual physical native traces

The reached trace contains physical checks for each yielded instruction.
Those checks derive the semantic, cost, and loaded-field invariants at its
literal returned state. No semantic result law or final invariant is an
input. Completion of a query remains a separate obligation.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeTraceEffects
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionRowsAllocation (Effects)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {A : Type} {width fuel : Nat}

/-- An actual return trace derives the physical effects needed by the current emptiness memo. -/
theorem effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {control : Control A} {before after : Checked width} {value : A}
    (trace : Trace fuel control before (.code (.pure value)) after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (costs : CostHeap before.native.machine.heap)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control before) :
    Good after ∧ Effects (physical before) (physical after) ∧
      Extension before.native.machine after.native.machine := by
  have done : execute (fuel + 1) control before = .done value after :=
    trace_done fuel control before after value trace.steps
  have inputs := trace.plan
  have heapInputs := SourceCurrentAllocatedNativePhysicalExecution.through_heap
    (fuel + 1) control before inputs
  have invariants := SourceCurrentAllocatedNativePhysicalCompletion.execute_invariants
    (fuel + 1) control before good inputs fields
  have finalSemantic := SourceCurrentAllocatedNativeSemanticHeap.execute_semantic
    (fuel + 1) control before semantic heapInputs
  have finalCosts := SourceCurrentAllocatedNativeCosts.execute_costs
    (fuel + 1) control before good.heap costs heapInputs
  have final : Good after ∧ Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (.done value after) := by
    simpa only [done, Outcome.state] using invariants
  have keptSemantic : SemanticReady after.native.machine.heap := by
    simpa only [done, Outcome.state] using finalSemantic
  have keptCosts : CostHeap after.native.machine.heap := by
    simpa only [done, Outcome.state] using finalCosts
  exact ⟨final.1, ⟨final.2.2.1,
    ⟨keptSemantic, keptCosts, final.1.operations, final.1.fields⟩,
    final.2.2.2.1⟩, final.2.1⟩

end MicroCFTA.SourceCurrentAllocatedNativeTraceEffects
