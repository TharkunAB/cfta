import MicroCFTA.InternedFreshOrdinaryCostRequest
import MicroCFTA.InternedFreshOrdinaryCostComposition

/-!
# Exact occurrence costs through full repaired source execution

The mutual source induction retains a weighted recursive heap. Both probes
and the fresh body use the induction hypothesis for their original syntax.
Canonical hits use the stored weighted observation. No callback cost law or
final cost heap is supplied by the caller.
-/
namespace MicroCFTA.InternedFreshOrdinaryCosts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedProvenance (Values depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryCostHeap
open InternedFreshOrdinaryCostExecutionFacts (Agrees Checked done_checked bind_checked)
open InternedRecordDepthShape (shape)
open InternedFreeOccurrenceRank InternedFreeOccurrenceNormalization
open InternedBinderProtocol (Reference)

mutual
/-- Every repaired source execution retains stored costs and derives all returned occurrence costs. -/
theorem build_costs [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : Heap state) :
    Checked (build expression environment state)
      (fun value => Agrees value (InternedOccurrenceCostSemantics.evaluate expression
        (environment.map shape) (environment.map costs))) := by
  cases expression with
  | empty =>
      rw [build]
      apply done_checked _ _ _ heap
      intro name count
      simp [costs, InternedOccurrenceCostSemantics.evaluate]
  | var index =>
      rw [build]
      apply done_checked _ _ _ heap
      intro name count
      simp only [InternedOccurrenceCostSemantics.evaluate]
      cases found : environment[index]? <;> simp [List.getElem?_map, found, costs]
  | node edges =>
      have verified := buildEdges_verified edges environment state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildEdges_costs edges environment state context cached heap)
      intro values after returned afterHeap same
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.edges edges
      apply done_checked
      · exact preserve after _ afterHeap (InternedShallowHeap.makeNode_noNewMu values after)
      · intro name count
        rw [InternedOccurrenceCostSemantics.evaluate]
        exact (InternedFreshOrdinaryCostExecutionFacts.makeNode_costs_surviving values after afterContext.normal.facts
          (verified.result values after returned) (name, count)).trans (same name count)
  | union members =>
      have verified := buildMany_verified members environment state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildMany_costs members environment state context cached heap)
      intro values after returned afterHeap same
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many members
      apply done_checked
      · exact preserve after _ afterHeap (InternedShallowHeap.makeUnion_noNewMu values after)
      · intro name count
        rw [InternedOccurrenceCostSemantics.evaluate]
        exact (InternedFreeOccurrenceExact.makeUnion_cost_iff values after afterContext.normal.facts.coherent
          afterContext.normal.facts.cached afterContext.normal.facts.linked afterContext.normal.live
          (verified.result values after returned) (name, count)).trans
          ((many_member values (name, count)).symm.trans (same name count))
  | binder smart body =>
      have checked : ∀ argument current, Context current environment → Available current (.reference argument) →
          InternedFreshOrdinaryDepthHeap.Heap current → Heap current →
          Checked (callback body environment argument current)
            (fun value => ∀ name count, name ≠ argument →
              ((name, count) ∈ costs value ↔ (name, count) ∈ InternedOccurrenceCostSemantics.captured body
                (environment.map shape) (environment.map costs))) := by
        intro argument current currentContext argumentAvailable currentCached currentHeap
        apply InternedFreshOrdinaryCostExecutionFacts.callback_checked body environment argument current currentContext argumentAvailable
        exact build_costs body (.reference argument :: environment) current
          (currentContext.local argument argumentAvailable) currentCached currentHeap
      have originalDepth := (InternedRecordDepthExecution.build_depth (.binder smart body) environment state context cached).heap
      have firstDepth := InternedRecordDepthExecution.callback_depth body environment .depth state context (depth_available state) cached
      have firstVerified := callback_verified body environment .depth state context.normal.facts (context.local .depth (depth_available state)).inputs
      rw [build]
      change Checked ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary) _
      apply bind_checked _ _ _ _ (checked .depth state context (depth_available state) cached heap)
      intro depth afterDepth depthDone depthHeap depthCosts
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
      have depthCached : InternedFreshOrdinaryDepthHeap.Heap afterDepth := by
        simpa only [depthDone, Outcome.state] using firstDepth.heap
      have depthObserved := firstDepth.result depth afterDepth depthDone
      have depthAvailable := firstVerified.result depth afterDepth depthDone
      have secondDepth := InternedRecordDepthExecution.callback_depth body environment (.uninterned (ordinaryLevel depth))
        afterDepth depthContext (ordinary_available afterDepth _) depthCached
      have secondVerified := callback_verified body environment (.uninterned (ordinaryLevel depth)) afterDepth
        depthContext.normal.facts (depthContext.local _ (ordinary_available afterDepth _)).inputs
      apply bind_checked _ _ _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available afterDepth _) depthCached depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap ordinaryCosts
      have finalContext : Context afterOrdinary environment := by
        simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth _)
      have finalCached : InternedFreshOrdinaryDepthHeap.Heap afterOrdinary := by
        simpa only [ordinaryDone, Outcome.state] using secondDepth.heap
      have ordinaryObserved := secondDepth.result ordinary afterOrdinary ordinaryDone
      have finalDepth : Available afterOrdinary depth := by
        simpa only [ordinaryDone, Outcome.state] using secondVerified.available depth depthAvailable
      have finalOrdinary := secondVerified.result ordinary afterOrdinary ordinaryDone
      have whole : build (.binder smart body) environment state =
          request smart depth ordinary (callback body environment) afterOrdinary := by
        rw [build]
        change ((callback body environment .depth state).bind _) = _
        rw [depthDone]
        change ((callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind _) = _
        rw [ordinaryDone]
        rfl
      rw [whole] at originalDepth
      have requested := InternedFreshOrdinaryCostRequest.request_checked smart body environment depth ordinary afterOrdinary
        finalContext ordinaryHeap finalCached finalDepth finalOrdinary
        (InternedOccurrenceCostSemantics.captured body (environment.map shape) (environment.map costs))
        depthCosts ordinaryCosts originalDepth
        (fun argument current currentContext argumentAvailable currentHeap currentCached =>
          checked argument current currentContext argumentAvailable currentCached currentHeap)
      have retention := InternedFreshOrdinaryCostComposition.binder_cost smart (InternedRecordDepthCallback.symbolic body environment)
        depth ordinary afterOrdinary finalContext.normal.facts.coherent finalDepth depthObserved.2 ordinaryObserved.2
      refine ⟨requested.heap, ?_⟩
      intro value final done name count
      exact (requested.result value final done name count).trans
        (InternedFreshOrdinaryCostComposition.binder_decoded smart body (environment.map shape) (environment.map costs)
          depth ordinary afterOrdinary finalContext.normal.facts.coherent finalDepth depthCosts ordinaryCosts retention name count)
termination_by sizeOf expression

/-- Ordered source members retain every original occurrence cost through all prior effects. -/
theorem buildMany_costs [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : Heap state) :
    Checked (buildMany expressions environment state)
      (fun values => ∀ name count, (name, count) ∈ manyCosts values ↔
        (name, count) ∈ InternedOccurrenceCostSemantics.evaluateMany expressions (environment.map shape) (environment.map costs)) := by
  cases expressions with
  | nil =>
      rw [buildMany]
      exact done_checked _ _ _ heap (by intro name count; simp [manyCosts, InternedOccurrenceCostSemantics.evaluateMany])
  | cons first rest =>
      have retained := (InternedRecordDepthExecution.build_depth first environment state context cached).heap
      rw [buildMany]
      apply bind_checked _ _ _ _ (build_costs first environment state context cached heap)
      intro value after returned afterHeap same
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.build first
      have afterCached : InternedFreshOrdinaryDepthHeap.Heap after := by simpa only [returned, Outcome.state] using retained
      apply bind_checked _ _ _ _ (buildMany_costs rest environment after afterContext afterCached afterHeap)
      intro values final done finalHeap tail
      apply done_checked _ _ _ finalHeap
      intro name count
      simp only [manyCosts, InternedOccurrenceCostSemantics.evaluateMany, List.mem_append]
      rw [same name count, tail name count]
termination_by sizeOf expressions

/-- Actual source edge schedules retain exactly the costs in their surviving ordered children. -/
theorem buildEdges_costs [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : Heap state) :
    Checked (buildEdges expressions environment state)
      (fun edges => ∀ name count, (name, count) ∈ edgeCosts (surviving edges) ↔
        (name, count) ∈ InternedOccurrenceCostSemantics.evaluateEdges expressions (environment.map shape) (environment.map costs)) := by
  cases expressions with
  | nil =>
      rw [buildEdges]
      exact done_checked _ _ _ heap (by intro name count; simp [surviving, edgeCosts, InternedOccurrenceCostSemantics.evaluateEdges])
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          have observed := InternedRecordDepthExecution.buildMany_depth children environment state context cached
          have verified := buildMany_verified children environment state context.normal.facts context.inputs
          rw [buildEdges]
          apply bind_checked _ _ _ _ (buildMany_costs children environment state context cached heap)
          intro values after returned afterHeap same
          have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many children
          have afterCached : InternedFreshOrdinaryDepthHeap.Heap after := by simpa only [returned, Outcome.state] using observed.heap
          have matched := observed.result values after returned
          have available := verified.result values after returned
          let actual := run (makeEdge symbol guard values) after
          have edgeContext : Context actual.2 environment := afterContext.edge symbol guard values available
          have edgeCached : InternedFreshOrdinaryDepthHeap.Heap actual.2 := afterCached
          have edgeHeap : Heap actual.2 := afterHeap
          have sameChildren : actual.1.children = values := InternedShallowValues.makeEdge_children symbol guard values after
            afterContext.normal.facts.coherent afterContext.normal.facts.cached available
          simp only [work, Outcome.bind]
          change Checked ((buildEdges rest environment actual.2).bind _) _
          apply bind_checked _ _ _ _ (buildEdges_costs rest environment actual.2 edgeContext edgeCached edgeHeap)
          intro edges final done finalHeap tail
          apply done_checked _ _ _ finalHeap
          intro name count
          rw [InternedFreshOrdinaryCostExecutionFacts.surviving_cons_costs, sameChildren,
            InternedFreshOrdinaryDepthComposition.children_empty matched, InternedOccurrenceCostSemantics.evaluateEdges]
          cases empty : (InternedDepthSemantics.evaluateMany children (environment.map shape)).any InternedDepthSemantics.Shape.isEmpty <;>
            simp [same name count, tail name count]
termination_by sizeOf expressions
end

/-- Empty-cache source execution derives the weighted heap even at a pending outer outcome. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap (build expression [] empty).state :=
  (build_costs expression [] empty empty_context InternedFreshOrdinaryDepthHeap.empty_heap empty_heap).heap

/-- Every external stored body occurrence has its exact cost in the actual repaired ordinary probe. -/
theorem closed_external_cost [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (name : Reference) (count : Nat) :
    ((name, count) ∈ costs body ∧ name ≠ .interned entry.identity) ↔
      ((name, count) ∈ costs ordinary ∧ name ≠ .uninterned (ordinaryLevel depth)) :=
  (closed_heap expression key entry body depth ordinary stored).external name count

/-- Every free occurrence of an actual stored Mu has its exact predecessor in the ordinary probe. -/
theorem closed_predecessor [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (name : Reference) (count : Nat) (occurrence : (name, count) ∈ costs (.mu entry body depth ordinary)) :
    ∃ prior, count = prior + 1 ∧ (name, prior) ∈ costs ordinary := by
  obtain ⟨prior, observed, same⟩ := (raw_costs entry body depth ordinary
    (closed_heap expression key entry body depth ordinary stored) name count).mp occurrence
  exact ⟨prior, same, observed.1⟩

/-- The actual ordinary probe has strictly smaller minimum occurrence rank than its open stored Mu. -/
theorem closed_probe_rank [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    rank ordinary < rank (.mu entry body depth ordinary) := by
  have context := (empty_context (Symbol := Symbol) (Guard := Guard)).build expression
  have available := context.normal.facts.cached.nodes key (.mu entry body depth ordinary) stored
  obtain ⟨name, occurrence⟩ := (rank_spec (.mu entry body depth ordinary) _ context.normal.facts.coherent available opened).1
  obtain ⟨prior, same, present⟩ := closed_predecessor expression key entry body depth ordinary stored name _ occurrence
  have bound := rank_le_cost ordinary name prior present
  omega

end MicroCFTA.InternedFreshOrdinaryCosts
