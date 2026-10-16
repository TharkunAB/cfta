import MicroCFTA.SourceCurrentAllocatedNativeTraceEffects
import MicroCFTA.SourceCurrentAllocatedConjunctionMemo
import MicroCFTA.SourceCurrentAllocatedNativeRequestResults

#print axioms MicroCFTA.SourceCurrentAllocatedNativeTraceEffects.effects
#check @MicroCFTA.SourceCurrentAllocatedNativeTraceEffects.effects

namespace MicroCFTA.TraceEffectsReviewProbe
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {width fuel : Nat} {A : Type}

-- The extra pure-return step preserves the exact trace-final state and loaded fields.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (before after : Checked width) (value : A)
    (trace : Trace fuel control before (.code (.pure value)) after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (costs : CostHeap before.native.machine.heap)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control before) :
    execute (fuel + 1) control before = .done value after ∧
      Good after ∧ SemanticReady after.native.machine.heap ∧ CostHeap after.native.machine.heap ∧
      SourceCurrentConjunctionEquality.Fields after.operations after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
      Extension before.native.machine after.native.machine := by
  obtain ⟨valid, effects, extension⟩ := SourceCurrentAllocatedNativeTraceEffects.effects trace good semantic costs fields
  exact ⟨trace_done fuel control before after value trace.steps, valid, effects.ready.semantic,
    effects.ready.costs, valid.fields, effects.grows, extension⟩

-- An actual original request supplies the returned value's availability before the current memo.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (request : NodeRequest Symbol Guard)
    (before queried : Checked width) (value : Value Symbol Guard)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) queried)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (costs : CostHeap before.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (left : SourceRecursiveIntersectionInputView.Original request.left)
    (right : SourceRecursiveIntersectionInputView.Original request.right)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo) :
    ∃ answer after saved,
      SourceCurrentConjunctionMemo.Call budget memo value (physical queried) answer after saved ∧
      SourceCurrentAllocatedConjunctionMemo.Receipt queried after ∧
      SourceCurrentConjunctionRowsAllocation.Effects (physical before) after ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver value answer ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  have fields : SourceCurrentAllocatedNativeFieldClosure.Fields
      (.code (requestNode request.domain request.left request.right)) before := fun _ => trivial
  obtain ⟨queriedGood, effects, _⟩ := SourceCurrentAllocatedNativeTraceEffects.effects trace good semantic costs fields
  have available := SourceCurrentAllocatedNativeRequestResults.node_result fuel request before queried value good.native left right trace
  have queriedIdle := SourceCurrentAllocatedNativeRunning.done_idle (fuel + 1) _ before queried value
    (by intro result; trivial) good.native.shape idle
    (trace_done fuel _ before queried value trace.steps)
  have queriedCorrect := SourceCurrentEmptinessMemo.grows formulas solver effects.keeps memo correct
  obtain ⟨answer, after, saved, actual, receipt, finalCorrect, sound, retained⟩ :=
    SourceCurrentAllocatedConjunctionMemo.finite formulas solver budget memo value queried queriedGood
      effects.ready.semantic effects.ready.costs queriedIdle available queriedCorrect
  exact ⟨answer, after, saved, actual, receipt, effects.trans receipt.effects, finalCorrect, sound, retained⟩

end MicroCFTA.TraceEffectsReviewProbe
