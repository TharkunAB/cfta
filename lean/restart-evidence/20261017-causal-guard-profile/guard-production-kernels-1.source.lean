import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryCoverage

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.CausalGuardKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open SourceCurrentConstrainedCapGuardSemantics (decode evaluate)
open SourceCurrentConstrainedCapGuardDepth (profile)
local notation "HistoryContext" => SourceCurrentConstrainedCapSourceHistory.Context
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
variable {Symbol Guard : Type}

/-- Full closed source construction produces its own guard heap and exact observation for arbitrary nested syntax. -/
theorem constructed [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expression : Syntax Symbol Guard) :
    ∃ (value : Value Symbol Guard) (after : State Symbol Guard),
      build expression [] empty = .done value after ∧ GuardHeap valid after ∧
      profile valid value = (evaluate valid expression ([] : List (SourceCurrentConstrainedCapGuardSemantics.Shape InternedBinderProtocol.Reference))).guardDepth ∧
      SourceCurrentConstrainedCapSourceHistory.Heap after := by
  obtain ⟨value, after, actual⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have checked := SourceCurrentConstrainedCapGuardExecution.build_profile valid expression [] empty
    SourceCurrentConstrainedCapSourceHistory.empty_context (SourceCurrentConstrainedCapGuardHeap.empty_heap valid)
  have guards : GuardHeap valid after := by simpa only [actual, Outcome.state] using checked.heap
  have history : SourceCurrentConstrainedCapSourceHistory.Heap after := by
    simpa only [actual, Outcome.state] using SourceCurrentConstrainedCapSourceHistory.closed_origins expression
  exact ⟨value, after, actual, guards, checked.result value after actual, history⟩

/-- A second actual source run consumes the first produced value and guard heap at the exact returned state. -/
theorem serial_captured [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (first second : Syntax Symbol Guard) :
    ∃ (value result : Value Symbol Guard) (middle after : State Symbol Guard),
      build first [] empty = .done value middle ∧
      build second [value] middle = .done result after ∧
      GuardHeap valid middle ∧ GuardHeap valid after ∧
      profile valid result = (evaluate valid second [decode valid value]).guardDepth := by
  obtain ⟨value, middle, firstDone, guards, _firstProfile, _history⟩ := constructed valid first
  have joint : HistoryContext middle [] := by
    simpa only [firstDone, Outcome.state] using SourceCurrentConstrainedCapSourceHistory.empty_context.build first
  have available := (build_verified first [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result value middle firstDone
  have context : HistoryContext middle [value] :=
    ⟨⟨joint.base.normal, (by intro chosen member; cases List.mem_singleton.mp member; exact available),
      joint.base.profiles, joint.base.freeNames⟩, joint.depth⟩
  have covered : Covered [] middle := by
    simpa only [firstDone, Outcome.state] using InternedFreshOrdinaryCoverage.build_covered first [] empty []
      InternedConstructorTemplates.empty_valid InternedRecordCoherence.empty_correct.2
  obtain ⟨result, after, secondDone⟩ := InternedRecordDepthCompletion.source_complete second [value] middle
    context.base context.depth covered
  have checked := SourceCurrentConstrainedCapGuardExecution.build_profile valid second [value] middle context guards
  have finalGuards : GuardHeap valid after := by simpa only [secondDone, Outcome.state] using checked.heap
  exact ⟨value, result, middle, after, firstDone, secondDone, guards, finalGuards,
    checked.result result after secondDone⟩

#print axioms constructed
#check @constructed
#print axioms serial_captured
#check @serial_captured
end MicroCFTA.CausalGuardKernels
