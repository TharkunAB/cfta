import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
import MicroCFTA.SourceCurrentAllocatedNativeCosts
import MicroCFTA.SourceCurrentConjunctionRowsAllocation

/-!
# Physical conjunction readiness from actual checked native execution

Initial semantic, cost, and allocated-field invariants follow the same
actual checked execution. Every returned state derives conjunction readiness.
The reached native input plan retains its word and finish-receipt checks.
This result does not assume completion or replace the checked native engine.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeEffects
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula

/-- The conjunction worker reads the actual constructor heap and equality-operation cache. -/
def physical (state : Checked width) : Physical := ⟨state.native.machine.heap, state.operations⟩

/-- Initial conjunction readiness supplies the physical parts of checked native validity. -/
theorem state_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (state : Checked width)
    (native : SourceEqualityNativeDemandProvenance.Valid holds state.native) (ready : Ready (physical state)) :
    SourceEqualityNativeDemandValidity.StateValid holds state :=
  ⟨native, ready.semantic.ready, ready.valid⟩

/-- All actual finite outcomes derive conjunction readiness and retain their complete native histories. -/
theorem execute_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : Checked width)
    (native : SourceEqualityNativeDemandProvenance.Valid holds state.native) (ready : Ready (physical state))
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control state)
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough holds fuel control state) :
    Effects (physical state) (physical (execute fuel control state).state) ∧
      SourceEqualityNativeDemandProvenance.Valid holds (execute fuel control state).state.native ∧
      SourceRecursiveIntersectionKernel.Extension state.native.machine (execute fuel control state).state.native.machine ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (execute fuel control state) := by
  have valid := state_valid holds state native ready
  obtain ⟨finalValid, extension, keeps, growth, annotations, _⟩ :=
    SourceCurrentAllocatedNativeFieldExecution.execute_invariants holds fuel control state valid ready.fields fields inputs
  have semantic := SourceCurrentAllocatedNativeSemanticHeap.execute_semantic_of_inputs holds fuel control state ready.semantic inputs
  have costs := SourceCurrentAllocatedNativeCosts.execute_costs_of_inputs holds fuel control state valid ready.costs inputs
  exact ⟨⟨keeps, ⟨semantic, costs, finalValid.operations, annotations.1⟩, growth⟩,
    finalValid.native, extension, annotations⟩

end MicroCFTA.SourceCurrentAllocatedNativeEffects
