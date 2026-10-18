import MicroCFTA.SourceCurrentSelectedPrimaryOrigins
import MicroCFTA.SourceCurrentSelectedRenewalBoundary
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
namespace MicroCFTA.SelectedPrimaryKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceCurrentAllocatedRecordScanWorker (scan select)
open SourceCurrentAllocatedScanWorker (Outcome gate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "emptyFourth" => SourceCurrentEmptinessMemo.empty
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "ClassTrace" => EndpointStatefulGateTrace.ClassTrace source reaches
local notation "PathTrace" => EndpointStatefulGateTrace.PathTrace source reaches
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- A source-built repeated selected record derives its actual end gate and normality. -/
theorem actual_repeated_selected :
    ∃ (program : Syntax Symbol Guard) (root first second : Node) (heap : State Symbol Guard)
      (before : Checked 10) (record : SourceEqualityClassOrder.Record),
      InternedFreshOrdinaryConstruction.build program [] empty = .done root heap ∧
      children root = [first,second] ∧ before.native.machine.heap = heap ∧
      SourceCurrentNativeOperationHeap.Good before ∧
      InternedNestedProvenance.Values before.native.machine.heap [first,second] ∧
      record.paths = [[0],[1]] ∧
      scan 8 0 0 0 0 0 [first,second] [record,record] before emptyFourth =
        .done (none,[record,record]) before emptyFourth ∧
      ClassTrace [first,second] record.paths before.native.machine.heap false before.native.machine.heap ∧
      SourceCurrentRequiredUnionNormal.UnionNormal before.native.machine.heap ∧
      PathTrace [first,second] [0] before.native.machine.heap false before.native.machine.heap := by
  obtain ⟨program,root,first,second,_result,_next,heap,before,_after,_saved,record,_outputs,
    _row,_nextRow,_competing,_classes,_inherited,_combined,built,children,entry,good,available,
    paths,_coherent,_nontrivial,primary,_rest⟩ :=
    SourceCurrentSelectedRenewalBoundary.selected_competing_continuation
  have known : InternedNestedProvenance.Values before.native.machine.heap [first,second] := by
    rw [entry]
    exact available
  have actual : scan 8 0 0 0 0 0 [first,second] [record,record] before emptyFourth =
      .done (none,[record,record]) before emptyFourth := by
    simp only [scan,gate,ite_true,primary,Outcome.bind,Bool.false_eq_true,ite_false,select]
  have normal : SourceCurrentRequiredUnionNormal.UnionNormal before.native.machine.heap := by
    have initial := SourceCurrentRequiredUnionNormal.source program
    rw [built] at initial
    rw [entry]
    exact initial
  have selected : record ∈ [record,record] := List.mem_cons_self
  have member : [0] ∈ record.paths := by rw [paths]; exact List.mem_cons_self
  have inherited := SourceCurrentSelectedPrimaryOrigins.selected_source actual good known normal selected member
  exact ⟨program,root,first,second,heap,before,record,built,children,entry,good,known,paths,actual,
    SourceCurrentSelectedPrimaryOrigins.selected_class actual good known record selected,inherited⟩
end MicroCFTA.SelectedPrimaryKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

#check @MicroCFTA.SelectedPrimaryKernels.actual_repeated_selected
#print MicroCFTA.SelectedPrimaryKernels.actual_repeated_selected
#print axioms MicroCFTA.SelectedPrimaryKernels.actual_repeated_selected
