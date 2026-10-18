import MicroCFTA.SourceCurrentOuterInheritedGain
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceEqualityNormalizationReceipt

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

namespace MicroCFTA.OuterInheritedGainKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
open SourceCurrentOuterPrefixInvariants (Good)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached Step)
open SourceCurrentOuterInheritedDescent (pathHeight)
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
private def own : Guard := ⟨some [[[0,0],[0,1]]],.top⟩
private def crossing : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def expression : Syntax Symbol Guard := .node [.mk ("parent",.top) own [leaf,leaf]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def child : Node := ((InternedProbeProvenance.children value)[0]?).getD .empty
private def edge := ((nodeEdges value)[0]?).getD (run (makeEdge ("parent",.top) own [child,child]) heap).1
private def first := SourceEqualityConstraintAllocation.construct own.equalities Cache.emptyState
private def ownValue : EqValue := match first.1 with | .ok value => value | .error _ => .contradiction
private def second := SourceEqualityConstraintAllocation.construct plain.equalities first.2
private def emptyValue : EqValue := match second.1 with | .ok value => value | .error _ => .contradiction
private def third := SourceEqualityConstraintAllocation.construct crossing.equalities second.2
private def inherited : EqValue := match third.1 with | .ok value => value | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial third.2
private def checked : SourceEqualityNativeDemand.State 4 :=
  ⟨SourceRecursiveIntersectionThunks.initial 4 ⟨heap,Cache.emptyState⟩,operations⟩
private def cold := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private noncomputable def prefix := SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited cold.checked.operations
private def combined : EqValue := match prefix.1 with | .ok (some value) => value | _ => .contradiction
private noncomputable def middle := SourceCurrentAllocatedPartialGraph.prefixState cold edge inherited
private def descended := SourceCurrentAllocatedPartialGraph.descend middle combined 0
private def candidate : NodeRequest := ⟨descended.1,child⟩
private def final := descended.2
private theorem constructed : built = .done value heap := by
  obtain ⟨result,after,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,value,heap,done,InternedNestedConstruction.Outcome.state]
private theorem first_done : first = (.ok ownValue,first.2) := by cbv
private theorem second_done : second = (.ok emptyValue,second.2) := by cbv
private theorem third_done : third = (.ok inherited,third.2) := by cbv
private theorem own_cached : SourceEqualityGuardReadback.Cached own.equalities := by
  intro classes same
  cases same
  cbv
private theorem crossing_cached : SourceEqualityGuardReadback.Cached crossing.equalities := by
  intro classes same
  cases same
  cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState third.2 [own,plain,crossing] := by
  have firstHistory := SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) own_cached first_done
  have secondHistory := SourceEqualityOriginalAllocationHistory.History.construct
    firstHistory SourceEqualityGuardReadback.empty_cached second_done
  exact SourceEqualityOriginalAllocationHistory.History.construct secondHistory crossing_cached third_done
private theorem initial : SourceCurrentConjunctionClassScan.Ready checked ∧ Available heap value := by
  have produced := SourceCurrentConjunctionClassHistoryEntry.constructed 4 history Cache.empty_valid expression
    (fun guard member => by
      have included : guard = own ∨ guard = plain := by simpa [expression,leaf,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards] using member
      rcases included with rfl | rfl
      · exact .head _
      · exact .tail _ (.head _)) value heap constructed
  exact ⟨produced.1,produced.2.1⟩
private theorem inherited_ready : SourceEqualityConstraintAllocation.Ready operations.constraints inherited := by
  obtain ⟨result,after,done,_,ready,_,_,_⟩ := SourceEqualityConstraintAllocation.construct_complete
    crossing.equalities crossing_cached second.2 (history.verified Cache.empty_valid).1
  obtain ⟨same,state⟩ := Prod.mk.inj (done.symm.trans third_done)
  cases Except.ok.inj same
  cases state
  exact ready
private theorem cold_good : Good cold := SourceCurrentOuterPrefixInvariants.initial checked _ _
  (SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked initial.1.good) initial.1.semantic initial.1.costs)
  (SourceCurrentMemoMergeEffects.stored_empty heap)
  (SourceCurrentMuReconstructionEffects.constructed expression value heap constructed)
private theorem edge_resident : EdgeResident heap edge := by
  have found : edge ∈ nodeEdges value := by cbv; exact .head _
  exact resident_edges heap initial.1.semantic.1.normal.facts.linked value initial.2.resident edge found
private theorem actual_prefix : prefix.1 = .ok (some combined) := by cbv
private theorem actual_reached : Reached 0 0 0 0 0 0 0 0 0 0
    (.descendants 1 inherited edge cold) (.node 0 candidate final) := by
  have exposed : Reached 0 0 0 0 0 0 0 0 0 0 (.descendants 1 inherited edge cold)
      (.children 1 combined edge.children middle) := .snoc (.refl _) (.descendants_children actual_prefix)
  have walked := Reached.snoc exposed (Step.children_walk (by cbv; intro impossible; cases impossible))
  have last : Step 0 0 0 0 0 0 0 0 0 0 (.walk 1 combined 0 edge.children middle) (.node 0 candidate final) := by
    change Step 0 0 0 0 0 0 0 0 0 0 (.walk 1 combined 0 (child :: [child]) middle) (.node 0 candidate final)
    exact .walk_head
  exact .snoc walked last

private theorem proof :
    built = .done value heap ∧ Good cold ∧
      Reached 0 0 0 0 0 0 0 0 0 0 (.descendants 1 inherited edge cold) (.node 0 candidate final) ∧
      Good final ∧ SourceCurrentEqualityOperationFixed.FixedPayload candidate.inherited.payload ∧
      pathHeight inherited = 1 ∧ pathHeight combined = 2 ∧ candidate.inherited = inherited ∧
      SourceCompactGuards.sourceEqualities edge.entry.key.constraint = some [[[0,0],[0,1]]] := by
  have current := SourceCurrentOuterPrefixInvariants.reached actual_reached cold_good ⟨inherited_ready,edge_resident⟩
  have fixed := SourceCurrentOuterInheritedGain.child_fixed actual_reached cold_good inherited_ready edge_resident
  exact ⟨constructed,cold_good,actual_reached,current.1,fixed,by cbv,by cbv,by cbv,by cbv⟩

/-- A source-built crossing inherited class returns after a real own-field height gain and indexed child descent. -/
theorem crossing_dispatch :
    built = .done value heap ∧ Good cold ∧
      Reached 0 0 0 0 0 0 0 0 0 0 (.descendants 1 inherited edge cold) (.node 0 candidate final) ∧
      Good final ∧ SourceCurrentEqualityOperationFixed.FixedPayload candidate.inherited.payload ∧
      pathHeight inherited = 1 ∧ pathHeight combined = 2 ∧ candidate.inherited = inherited ∧
      SourceCompactGuards.sourceEqualities edge.entry.key.constraint = some [[[0,0],[0,1]]] := proof

end MicroCFTA.OuterInheritedGainKernels
