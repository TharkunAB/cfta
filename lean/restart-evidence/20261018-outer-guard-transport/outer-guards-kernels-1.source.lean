import MicroCFTA.SourceCurrentOuterGuardHeapReturns
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry

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
set_option cbv.maxSteps 10000000

namespace MicroCFTA.OuterGuardHeapKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants (Good NodeReady EdgeReady)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached Step)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq Node := by classical exact inferInstance
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def plain : Guard := ⟨some [],.top⟩
private def positive : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .mu (.node [
  .mk ("leaf",.top) plain [],.mk ("next",.top) plain [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("pair",.top) positive [leaf,leaf]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def child : Node := ((InternedProbeProvenance.children value)[0]?).getD .empty
private def row := ((nodeEdges value)[0]?).getD (run (makeEdge ("pair",.top) positive [child,child]) heap).1
private def first := SourceEqualityConstraintAllocation.construct positive.equalities Cache.emptyState
private def positiveValue : EqValue := match first.1 with | .ok value => value | .error _ => .contradiction
private def second := SourceEqualityConstraintAllocation.construct plain.equalities first.2
private def inherited : EqValue := match second.1 with | .ok value => value | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial second.2
private def checked : SourceEqualityNativeDemand.State 4 :=
  ⟨SourceRecursiveIntersectionThunks.initial 4 ⟨heap,Cache.emptyState⟩,operations⟩
private def cold := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private def request : NodeRequest := ⟨inherited,value⟩
private noncomputable def execution := nodeCall 6 8 8 8 8 8 8 8 8 8 0 request cold
private noncomputable def after := execution.state
private def edgeRequest : EdgeRequest := ⟨inherited,row⟩
private theorem constructed : built = .done value heap := by
  obtain ⟨result,after,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,value,heap,done,InternedNestedConstruction.Outcome.state]
private theorem first_done : first = (.ok positiveValue,first.2) := by cbv
private theorem second_done : second = (.ok inherited,second.2) := by cbv
private theorem positive_cached : SourceEqualityGuardReadback.Cached positive.equalities := by
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized
    (show EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] by cbv)
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState second.2 [positive,plain] := by
  exact SourceEqualityOriginalAllocationHistory.History.construct
    (SourceEqualityOriginalAllocationHistory.History.construct (.start Cache.emptyState) positive_cached first_done)
    SourceEqualityGuardReadback.empty_cached second_done
private theorem initial : SourceCurrentConjunctionClassScan.Ready checked ∧ Available heap value := by
  have produced := SourceCurrentConjunctionClassHistoryEntry.constructed 4 history Cache.empty_valid expression
    (fun guard member => by
      have included : guard = positive ∨ guard = plain := by
        simpa [expression,leaf,SourceEqualityConstraintOrigins.guards,
          SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards] using member
      rcases included with rfl | rfl
      · exact .head _
      · exact .tail _ (.head _)) value heap constructed
  exact ⟨produced.1,produced.2.1⟩
private theorem inherited_ready : SourceEqualityConstraintAllocation.Ready operations.constraints inherited := by
  have firstHistory := SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) positive_cached first_done
  obtain ⟨result,after,done,_,ready,_,_,_⟩ := SourceEqualityConstraintAllocation.construct_complete
    plain.equalities SourceEqualityGuardReadback.empty_cached first.2 (firstHistory.verified Cache.empty_valid).1
  obtain ⟨same,state⟩ := Prod.mk.inj (done.symm.trans second_done)
  cases Except.ok.inj same
  cases state
  exact ready
private theorem cold_good : Good cold := SourceCurrentOuterPrefixInvariants.initial checked _ _
  (SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked initial.1.good) initial.1.semantic initial.1.costs)
  (SourceCurrentMemoMergeEffects.stored_empty heap)
  (SourceCurrentMuReconstructionEffects.constructed expression value heap constructed)
private theorem row_resident : EdgeResident heap row := by
  have found : row ∈ nodeEdges value := by cbv; exact .head _
  exact resident_edges heap cold_good.checked.heap.semantic.1.normal.facts.linked
    value initial.2.resident row found
private theorem actual : execution = .done value after := by cbv
private theorem complete_facts : Good after ∧
    SourceCurrentLowerOperationInvariants.Effect cold.checked after.checked ∧
    Available after.checked.native.machine.heap value :=
  SourceCurrentOuterPrefixInvariants.node_done actual cold_good ⟨inherited_ready,initial.2⟩
private theorem edge_ready : EdgeReady after edgeRequest := by
  exact ⟨inherited_ready.grows complete_facts.2.1.operations.constraint_growth,
    edge_grows heap _ complete_facts.2.1.keeps.growth row row_resident⟩
private theorem ready_hit : beginEdge edgeRequest after = (0,.ready row,after) := by cbv
private theorem warm : edgeCall 0 8 8 8 8 8 8 8 8 8 0 edgeRequest after = .done row after :=
  edgeCall_ready 0 8 8 8 8 8 8 8 8 8 0 edgeRequest after after 0 row ready_hit
private theorem phase_reached : Reached 8 8 8 8 8 8 8 8 8 0
    (.rows 1 inherited [row] after) (.descendants 0 inherited row after) :=
  Reached.snoc (.refl _) (Step.rows_edge warm)
private theorem positive_mu : row.entry.key.constraint = positive ∧
    (∃ entry body depth ordinary, child = .mu entry body depth ordinary) := by cbv; exact ⟨rfl,_,_,_,_,rfl⟩

/-- A constructed recursive source retains every causal guard predicate through cold and warm calls and a prefix. -/
theorem recursive_cold_warm_prefix (annotation : Guard → Prop) :
    Good cold ∧ NodeReady cold request ∧
      execution = .done value after ∧
      SourceCurrentConstrainedCapGuardHeap.Heap annotation cold.checked.native.machine.heap ∧
      SourceCurrentConstrainedCapGuardHeap.Heap annotation after.checked.native.machine.heap ∧
      beginEdge edgeRequest after = (0,.ready row,after) ∧
      edgeCall 0 8 8 8 8 8 8 8 8 8 0 edgeRequest after = .done row after ∧
      row.entry.key.constraint = positive ∧
      (∃ entry body depth ordinary, child = .mu entry body depth ordinary) ∧
      Reached 8 8 8 8 8 8 8 8 8 0 (.rows 1 inherited [row] after) (.descendants 0 inherited row after) ∧
      SourceCurrentConstrainedCapGuardHeap.Heap annotation
        (SourceCurrentOuterActiveAncestry.caller (.descendants 0 inherited row after)).checked.native.machine.heap := by
  have initialGuards : SourceCurrentConstrainedCapGuardHeap.Heap annotation heap := by
    simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap annotation expression
  have retained := SourceCurrentOuterGuardHeapReturns.node_done annotation actual cold_good
    ⟨inherited_ready,initial.2⟩ initialGuards
  have warmed := SourceCurrentOuterGuardHeapReturns.edge_done annotation warm complete_facts.1 edge_ready retained
  have earlierInputs : SourceCurrentOuterPrefixInvariants.Inputs (.rows 1 inherited [row] after) :=
    ⟨edge_ready.1,by intro edge member; cases List.mem_singleton.mp member; exact edge_ready.2⟩
  exact ⟨cold_good,⟨inherited_ready,initial.2⟩,actual,initialGuards,retained,ready_hit,warm,
    positive_mu.1,positive_mu.2,phase_reached,
    SourceCurrentOuterGuardHeapReturns.reached annotation phase_reached complete_facts.1 earlierInputs warmed⟩

end MicroCFTA.OuterGuardHeapKernels
