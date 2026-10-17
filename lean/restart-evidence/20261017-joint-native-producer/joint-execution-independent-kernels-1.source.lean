import MicroCFTA.SourceCurrentConstrainedCapKernelJointExecution

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.JointExecutionIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionKernel
open SourceCurrentConstrainedCapKernelJoint
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapGuardDepth (profile)

private def recursivePlan : Syntax Nat Bool := .binder false (.node [.mk 0 true [], .mk 1 true [.var 0]])
private def constrainedPlan : Syntax Nat Bool := .node [.mk 1 false [.node [.mk 0 true []]]]
private def built := InternedFreshOrdinaryConstruction.buildMany [recursivePlan, constrainedPlan] [] (empty : State Nat Bool)
private def source := built.state
private def values := match built with | .done values _ => values | .pending .. => []
private def left := values[0]?.getD .empty
private def right := values[1]?.getD .empty
private def machine : Machine Nat Bool := ⟨source, Cache.emptyState⟩

set_option cbv.maxSteps 100000000 in
private theorem source_computed : built = .done [left, right] source := by cbv

set_option cbv.maxSteps 100000000 in
private theorem closed_computed : left.free = [] ∧ right.free = [] := by cbv

set_option cbv.maxSteps 100000000 in
private theorem query_computed :
    (match execute true (· && ·) 16 IntersectionEmptyDomain.emptyDomain left right machine with
    | .done value _ => value = right | .failed .. => False) := by cbv

/-- Actual productive Mu intersection derives the same constrained result and every joint local law. -/
theorem productive_mixed_query :
    ∃ after, built = .done [left, right] source ∧
      execute true (· && ·) 16 IntersectionEmptyDomain.emptyDomain left right machine = .done right after ∧
      Cap (fun guard : Bool => guard = true) 1 right ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified
        (SourceCurrentConstrainedCapPairOccurrences.sourceWeight (fun guard : Bool => guard = true) source)
        (SourceCurrentConstrainedCapNonplainRank.pairRank (fun guard : Bool => guard = true) left right) right ∧
      SourceRecursiveIntersectionResultScope.Scope [] right ∧
      SourceCurrentConstrainedCapGuardHeap.Heap (fun guard : Bool => guard = true) after.heap ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap after.heap ∧ Grows source after.heap := by
  have actual : InternedFreshOrdinaryConstruction.buildMany [recursivePlan, constrainedPlan] [] empty =
      .done [left, right] source := source_computed
  have physical := InternedFreshOrdinaryFacts.buildMany_verified [recursivePlan, constrainedPlan] [] (empty : State Nat Bool)
    InternedNestedFacts.empty_facts (by intro value absent; cases absent)
  have facts : Facts source := by simpa only [actual, Outcome.state] using physical.facts
  have available := physical.result [left, right] source actual
  have leftAvailable := available left List.mem_cons_self
  have rightAvailable := available right (List.mem_cons_of_mem _ List.mem_cons_self)
  have jointContext := SourceCurrentConstrainedCapSourceHistory.empty_context.many [recursivePlan, constrainedPlan]
  have semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap source :=
    ⟨by simpa only [actual, Outcome.state] using jointContext.base,
      by simpa only [actual, Outcome.state] using jointContext.depth⟩
  have checked := SourceCurrentConstrainedCapGuardExecution.buildMany_profile (fun guard : Bool => guard = true)
    [recursivePlan, constrainedPlan] [] (empty : State Nat Bool) SourceCurrentConstrainedCapSourceHistory.empty_context
    (SourceCurrentConstrainedCapGuardHeap.empty_heap _)
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap (fun guard : Bool => guard = true) source := by
    simpa only [actual, Outcome.state] using checked.heap
  have matched := checked.result [left, right] source actual
  have observed : profile (fun guard : Bool => guard = true) left = some 0 ∧
      profile (fun guard : Bool => guard = true) right = some 1 := by
    classical
    cases matched with
    | cons first rest =>
        cases rest with
        | cons second tail =>
            constructor
            · simpa [recursivePlan, SourceCurrentConstrainedCapGuardSemantics.evaluateMany,
                SourceCurrentConstrainedCapGuardSemantics.evaluate, SourceCurrentConstrainedCapGuardSemantics.evaluateEdges,
                SourceCurrentConstrainedCapGuardSemantics.edge, SourceCurrentConstrainedCapGuardSemantics.binder,
                SourceCurrentConstrainedCapGuardSemantics.reference, SourceCurrentConstrainedCapGuardSemantics.Shape.map,
                SourceCurrentConstrainedCapGuardSemantics.combineMany, SourceCurrentConstrainedCapGuardSemantics.combine,
                InternedDepthSemantics.edge, InternedDepthSemantics.binder, InternedDepthSemantics.combine,
                InternedDepthSemantics.combineMany, InternedDepthSemantics.Shape.isEmpty, InternedDepthSemantics.Shape.free,
                InternedDepthSemantics.Shape.map, InternedDepthSemantics.hasLocal,
                SourceCurrentConstrainedCapGuardDepth.join, SourceCurrentConstrainedCapGuardDepth.raise,
                SourceCurrentConstrainedCapGuardDepth.guardCost] using first.2
            · simpa [constrainedPlan, SourceCurrentConstrainedCapGuardSemantics.evaluateMany,
                SourceCurrentConstrainedCapGuardSemantics.evaluate, SourceCurrentConstrainedCapGuardSemantics.evaluateEdges,
                SourceCurrentConstrainedCapGuardSemantics.edge, SourceCurrentConstrainedCapGuardSemantics.combineMany,
                SourceCurrentConstrainedCapGuardSemantics.combine, InternedDepthSemantics.edge,
                InternedDepthSemantics.combine, InternedDepthSemantics.combineMany, InternedDepthSemantics.Shape.isEmpty,
                InternedDepthSemantics.Shape.free, SourceCurrentConstrainedCapGuardDepth.join,
                SourceCurrentConstrainedCapGuardDepth.raise, SourceCurrentConstrainedCapGuardDepth.guardCost] using second.2
  have leftCap : Cap (fun guard : Bool => guard = true) 1 left :=
    .plain 1 ((SourceCurrentConstrainedCapGuardDepth.profile_zero_iff _ _).mp observed.1)
  have rightCap : Cap (fun guard : Bool => guard = true) 1 right :=
    (SourceCurrentConstrainedCapGuardDepth.profile_minimal _ _ _ observed.2 1).mpr (Nat.le_refl _)
  have context : Context (fun guard : Bool => guard = true) source machine :=
    ⟨⟨facts, Cache.empty_valid⟩, semantic, guards, grows_refl _, extends_refl _⟩
  have inputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source facts IntersectionEmptyDomain.emptyDomain
    left right leftAvailable rightAvailable closed_computed.1 closed_computed.2
  have calls := execute_joint (fun guard : Bool => guard = true) source facts true (· && ·) rfl
    (by intro first second firstTrue secondTrue; simp [firstTrue, secondTrue]) 16
  have result := calls 1 IntersectionEmptyDomain.emptyDomain left right machine context (empty_domain _)
    (SourceCurrentConstrainedCapOriginalSupport.empty _ _) inputs leftCap rightCap
  cases done : execute true (· && ·) 16 IntersectionEmptyDomain.emptyDomain left right machine with
  | failed failure stopped => simpa only [done] using query_computed
  | done value after =>
      have same : value = right := by simpa only [done] using query_computed
      subst value
      have returned := result right after done
      exact ⟨after, source_computed, rfl, returned.2.2.1, returned.2.2.2.1, returned.2.2.2.2,
        returned.1.guards, returned.1.semantic, returned.1.growth⟩

#print axioms productive_mixed_query
#check @productive_mixed_query
end MicroCFTA.JointExecutionIndependent
