import MicroCFTA.SourceCurrentOuterRowFieldOrigins
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

namespace MicroCFTA.OuterRowFieldKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants (Good NodeReady EdgeReady)
open SourceCurrentOuterRowFieldOrigins (Origins Fields)
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
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
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
private theorem origins : Origins after := SourceCurrentOuterRowFieldOrigins.node_done
  actual cold_good ⟨inherited_ready,initial.2⟩ (SourceCurrentOuterRowFieldOrigins.initial checked _ _)
private theorem edge_ready : EdgeReady after edgeRequest := by
  exact ⟨inherited_ready.grows complete_facts.2.1.operations.constraint_growth,
    edge_grows heap _ complete_facts.2.1.keeps.growth row row_resident⟩
private theorem ready_hit : beginEdge edgeRequest after = (0,.ready row,after) := by cbv
private theorem warm : edgeCall 0 8 8 8 8 8 8 8 8 8 0 edgeRequest after = .done row after :=
  edgeCall_ready 0 8 8 8 8 8 8 8 8 8 0 edgeRequest after after 0 row ready_hit
private theorem phase_reached : Reached 8 8 8 8 8 8 8 8 8 0
    (.rows 1 inherited [row] after) (.descendants 0 inherited row after) :=
  Reached.snoc (.refl _) (Step.rows_edge warm)
private theorem row_positive : row.entry.key.constraint = positive := by cbv
private theorem positive_not_top : positive ≠ SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula) := by
  intro same
  have falseEquality := congrArg SourceSymbolicIndex.Constraint.equalities same
  cases falseEquality
private theorem fixture :
    Good cold ∧ Origins cold ∧ NodeReady cold request ∧
      execution = .done value after ∧ Good after ∧ Origins after ∧
      beginEdge edgeRequest after = (0,.ready row,after) ∧
      edgeCall 0 8 8 8 8 8 8 8 8 8 0 edgeRequest after = .done row after ∧
      Fields row.entry.key.symbol row.entry.key.constraint row ∧
      row.entry.key.constraint = positive ∧
      row.entry.key.constraint ≠ SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula) ∧
      Reached 8 8 8 8 8 8 8 8 8 0 (.rows 1 inherited [row] after) (.descendants 0 inherited row after) ∧
      Origins (SourceCurrentOuterActiveAncestry.caller (.descendants 0 inherited row after)) := by
  have retained := SourceCurrentOuterRowFieldOrigins.edge_call warm complete_facts.1 edge_ready origins
  have earlierInputs : SourceCurrentOuterPrefixInvariants.Inputs (.rows 1 inherited [row] after) :=
    ⟨edge_ready.1,by intro edge member; cases List.mem_singleton.mp member; exact edge_ready.2⟩
  exact ⟨cold_good,SourceCurrentOuterRowFieldOrigins.initial checked _ _,⟨inherited_ready,initial.2⟩,
    actual,complete_facts.1,origins,ready_hit,warm,retained.2,row_positive,
    by rw [row_positive]; exact positive_not_top,phase_reached,
    SourceCurrentOuterRowFieldOrigins.reached phase_reached complete_facts.1 earlierInputs origins⟩

/-- An actual cold node return supplies row origins before a positive-field warm edge hit and descendants prefix. -/
theorem cold_node_warm_positive_row :
    Good cold ∧ Origins cold ∧ NodeReady cold request ∧
      execution = .done value after ∧ Good after ∧ Origins after ∧
      beginEdge edgeRequest after = (0,.ready row,after) ∧
      edgeCall 0 8 8 8 8 8 8 8 8 8 0 edgeRequest after = .done row after ∧
      Fields row.entry.key.symbol row.entry.key.constraint row ∧
      row.entry.key.constraint = positive ∧
      row.entry.key.constraint ≠ SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula) ∧
      Reached 8 8 8 8 8 8 8 8 8 0 (.rows 1 inherited [row] after) (.descendants 0 inherited row after) ∧
      Origins (SourceCurrentOuterActiveAncestry.caller (.descendants 0 inherited row after)) := fixture

end MicroCFTA.OuterRowFieldKernels

#check @MicroCFTA.OuterRowFieldKernels.cold_node_warm_positive_row
#print MicroCFTA.OuterRowFieldKernels.cold_node_warm_positive_row
#print axioms MicroCFTA.OuterRowFieldKernels.cold_node_warm_positive_row
