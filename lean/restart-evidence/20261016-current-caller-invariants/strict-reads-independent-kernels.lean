import MicroCFTA.SourceCurrentPrimaryReadsCounterexample
import MicroCFTA.SourceCurrentAllocatedPrimaryCompletion
import MicroCFTA.SourceCurrentAllocatedQueryReadValidity

namespace MicroCFTA.StrictReadsIndependentKernels
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- The old counterexample cannot be admitted as a strict source read. -/
theorem historical_is_not_strict :
    EndpointMemoGateTrace.NodeReads SourceCurrentPrimaryReadsCounterexample.trace SourceCurrentPrimaryReadsCounterexample.initialMemos SourceCurrentPrimaryReadsCounterexample.finalMemos ∧
      ¬ SourceCurrentAllocatedPrimaryReads.NodeReads SourceCurrentPrimaryReadsCounterexample.trace SourceCurrentPrimaryReadsCounterexample.initialMemos SourceCurrentPrimaryReadsCounterexample.finalMemos := by
  refine ⟨SourceCurrentPrimaryReadsCounterexample.unanchored_reads, ?_⟩
  intro strict
  exact SourceCurrentPrimaryReadsCounterexample.final_invalid (SourceCurrentAllocatedGateReadValidity.primary_node strict SourceCurrentPrimaryReadsCounterexample.ready SourceCurrentPrimaryReadsCounterexample.available SourceCurrentPrimaryReadsCounterexample.initial_valid).valid

/-- The same actual resident gate trace constructs strict valid returned tables. -/
theorem corrected_actual_trace : ∃ saved,
    SourceCurrentAllocatedPrimaryReads.NodeReads SourceCurrentPrimaryReadsCounterexample.trace SourceCurrentPrimaryReadsCounterexample.initialMemos saved ∧ Valid SourceCurrentPrimaryReadsCounterexample.heap saved ∧
      ∃ fuel, EndpointStatefulGate.nodeMeets source reaches fuel [] (.node SourceCurrentPrimaryReadsCounterexample.entry SourceCurrentPrimaryReadsCounterexample.edges 1 []) SourceCurrentPrimaryReadsCounterexample.heap =
        .done (some (!(([] : List InternedBinderProtocol.Reference).isEmpty) ||
          reaches (.node SourceCurrentPrimaryReadsCounterexample.entry SourceCurrentPrimaryReadsCounterexample.edges 1 []))) SourceCurrentPrimaryReadsCounterexample.heap := by
  obtain ⟨saved, strict, kept⟩ := SourceCurrentAllocatedPrimaryReads.lift_node [] _ SourceCurrentPrimaryReadsCounterexample.heap _ SourceCurrentPrimaryReadsCounterexample.heap SourceCurrentPrimaryReadsCounterexample.trace
    SourceCurrentPrimaryReadsCounterexample.ready SourceCurrentPrimaryReadsCounterexample.available SourceCurrentPrimaryReadsCounterexample.initialMemos SourceCurrentPrimaryReadsCounterexample.initial_valid
  exact ⟨saved, strict, kept.valid, SourceCurrentPrimaryReadsCounterexample.trace_complete⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- The primary receipt supplies the exact tables used by the secondary, seeded, and current-call suffix. -/
theorem primary_then_actual_query
    {paths : Class} {values : List (Value Symbol Guard)}
    {before middle : Checked width} {after : Physical} {primaryHeap anchor : State Symbol Guard}
    {value : Value Symbol Guard} {answer : Bool} {budget : Nat} {memo saved : Memo}
    {primary : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.native.machine.heap false primaryHeap}
    {gate : SourceCurrentSecondaryTrace.ClassTrace source values paths primaryHeap false anchor}
    {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap (advanceHeap before primaryHeap) anchor) value middle}
    {call : SourceCurrentConjunctionMemo.Call budget memo value (physical middle) answer after saved}
    {memos intermediate final : Memos}
    (first : SourceCurrentAllocatedPrimaryReads.ClassReads primary memos intermediate)
    (suffix : SourceCurrentConjunctionQueryGlobalMemos.QueryReads gate seeded call intermediate final)
    (proper : ∀ path ∈ paths, path ≠ [])
    (ranges : SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
      (advanceHeap (advanceHeap before primaryHeap) anchor))
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (valid : Valid before.native.machine.heap memos) :
    Valid after.heap final ∧ Ready (advancePhysical middle after) ∧ Effects (physical before) after ∧
      Values after.heap values ∧ SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  have prefixEffects := SourceCurrentConjunctionClassScan.primary_effects source reaches primary ready available
  have prefixMemos := SourceCurrentAllocatedGateReadValidity.primary_class first
    (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available valid
  have prefixCorrect := SourceCurrentEmptinessMemo.grows formulas solver prefixEffects.2.1.keeps memo correct
  obtain ⟨finalValid, finalReady, effects, finalValues, finalCorrect, retained⟩ :=
    SourceCurrentAllocatedQueryReadValidity.query suffix proper ranges prefixEffects.1 prefixEffects.2.2
      formulas solver prefixCorrect prefixMemos.valid
  exact ⟨finalValid, finalReady, prefixEffects.2.1.trans effects, finalValues, finalCorrect, retained⟩

#print axioms historical_is_not_strict
#print axioms corrected_actual_trace
#print axioms primary_then_actual_query
set_option pp.explicit true in
#check @historical_is_not_strict
set_option pp.explicit true in
#check @corrected_actual_trace
set_option pp.explicit true in
#check @primary_then_actual_query
end MicroCFTA.StrictReadsIndependentKernels
