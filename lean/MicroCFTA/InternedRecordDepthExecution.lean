import MicroCFTA.InternedRecordDepthCallback

/-!
# Actual source depth with arbitrary captured records

The complete syntax induction decodes each captured record. Every outcome
retains the depth heap. Each returned record has the exact interpreted
empty decision, cached depth, and deep-name membership.
-/
namespace MicroCFTA.InternedRecordDepthExecution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryDepthComposition
open InternedFreshOrdinaryDepthRequest (Checked done_checked bind_checked)
open InternedDepthSemantics
open InternedRecordDepthShape
open InternedRecordDepthCallback (symbolic captured uses callback_checked callback_free)
open InternedBinderProtocol (Reference)

mutual
/-- Full repaired source execution preserves the depth heap and derives each returned shape observation. -/
theorem build_depth [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (build expression environment state)
      (fun value => Observed value (evaluate expression (environment.map shape))) := by
  cases expression with
  | empty =>
      rw [build, evaluate]
      exact done_checked _ _ _ heap ⟨rfl, rfl, by simp [InternedDeepFreeDepth.deepNames]⟩
  | var index =>
      rw [build]
      apply done_checked _ _ _ heap
      cases found : environment[index]? with
      | none =>
          simp only [evaluate, List.getElem?_map, found, Option.map_none, Option.getD_none]
          exact ⟨rfl, rfl, by simp [InternedDeepFreeDepth.deepNames]⟩
      | some value =>
          simp only [evaluate, List.getElem?_map, found, Option.map_some, Option.getD_some]
          exact InternedRecordDepthShape.observed value state context.normal
            (context.inputs value (List.mem_of_getElem? found))
  | node edges =>
      have verified := buildEdges_verified edges _ state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildEdges_depth edges environment state context heap)
      intro values after returned afterHeap same
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.edges edges
      have available := verified.result _ _ returned
      have whole : build (.node edges) environment state =
          .done (run (makeNode values) after).1 (run (makeNode values) after).2 := by simp only [build, returned, Outcome.bind, work]
      apply done_checked
      · exact InternedFreshOrdinaryDepthHeap.preserve after _ afterHeap (InternedShallowHeap.makeNode_noNewMu values after)
      · exact ⟨InternedRecordDepthSource.source_empty _ environment state context _ _ whole,
          (InternedNormalizationDepthExact.makeNode_surviving_depth values after afterContext.normal.facts.coherent
            afterContext.normal.facts.linked available).trans (by simpa only [evaluate] using same),
          InternedRecordDepthSource.source_node_deep edges environment state context _ _ whole⟩
  | union members =>
      have verified := buildMany_verified members _ state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildMany_depth members environment state context heap)
      intro values after returned afterHeap matched
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many members
      apply done_checked
      · exact InternedFreshOrdinaryDepthHeap.preserve after _ afterHeap (InternedShallowHeap.makeUnion_noNewMu values after)
      · simpa only [evaluate] using union_observed values _ after afterContext (verified.result _ _ returned) matched
  | binder smart body =>
      have checked : ∀ argument current, Context current environment → Available current (.reference argument) →
          InternedFreshOrdinaryDepthHeap.Heap current →
          Checked (callback body environment argument current)
            (fun value => value.depth = (symbolic body environment).depth ∧
              InternedFreshOrdinaryDepthHeap.Observed (captured body environment)
                (uses body environment) argument value) := by
        intro argument current currentContext argumentAvailable currentHeap
        apply InternedRecordDepthCallback.callback_checked body environment argument current currentContext argumentAvailable
        exact build_depth body (.reference argument :: environment) current (by simpa only [List.map_cons] using currentContext.local argument argumentAvailable) currentHeap
      have fullFree := InternedFreshOrdinaryFreeNames.build_free (.binder smart body) _ state context.normal context.inputs context.freeNames context.profiles
      rw [build]
      change Checked ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary) _
      apply bind_checked _ _ _ _ (checked .depth state context (depth_available state) heap)
      intro depth afterDepth depthDone depthHeap depthObserved
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
      have depthVerified := callback_verified body _ .depth state context.normal.facts (context.local .depth (depth_available state)).inputs
      have depthAvailable := depthVerified.result _ _ depthDone
      apply bind_checked _ _ _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext (ordinary_available afterDepth _) depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap ordinaryObserved
      have finalContext : Context afterOrdinary environment := by
        simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth _)
      have ordinaryVerified := callback_verified body _ (.uninterned (ordinaryLevel depth)) afterDepth
        depthContext.normal.facts (depthContext.local _ (ordinary_available afterDepth _)).inputs
      have finalDepth : Available afterOrdinary depth := by simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth depthAvailable
      have finalOrdinary := ordinaryVerified.result _ _ ordinaryDone
      have whole : build (.binder smart body) environment state =
          request smart depth ordinary (callback body environment) afterOrdinary := by
        rw [build]
        change ((callback body environment .depth state).bind _) = _
        rw [depthDone]
        change ((callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind _) = _
        rw [ordinaryDone]
        rfl
      rw [whole] at fullFree
      have requested := InternedFreshOrdinaryDepthRequest.request_checked smart body _ depth ordinary afterOrdinary finalContext ordinaryHeap
        finalDepth finalOrdinary _ _ _ depthObserved.1 depthObserved.2 ordinaryObserved.2 fullFree.heap
        (fun argument current currentContext argumentAvailable currentHeap => checked argument current currentContext argumentAvailable currentHeap)
      have decoded := binder_shape smart (symbolic body environment) depth ordinary afterOrdinary finalContext.normal.facts.coherent finalDepth depthObserved.1
        depthObserved.2 ordinaryObserved.2
        (InternedRecordDepthCallback.callback_free body environment .depth state context (depth_available state) depth afterDepth depthDone)
        (InternedRecordDepthCallback.callback_free body environment (.uninterned (ordinaryLevel depth)) afterDepth depthContext (ordinary_available afterDepth _) ordinary afterOrdinary ordinaryDone)
      refine ⟨requested.heap, ?_⟩
      intro value after returned
      have observed := requested.result _ _ returned
      exact ⟨InternedRecordDepthSource.source_empty _ environment state context _ _ (whole.trans returned), observed.1.trans (by simpa only [evaluate, symbolic] using decoded.1),
        fun name => (observed.2 name).trans (by simpa only [evaluate, symbolic] using decoded.2 name)⟩
termination_by sizeOf expression

/-- Ordered source children retain their pure shape observations at every position. -/
theorem buildMany_depth [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (buildMany expressions environment state)
      (fun values => Matches values (evaluateMany expressions (environment.map shape))) := by
  cases expressions with
  | nil =>
      rw [buildMany, evaluateMany]
      exact done_checked _ _ _ heap .nil
  | cons first rest =>
      rw [buildMany]
      apply bind_checked _ _ _ _ (build_depth first environment state context heap)
      intro value after returned afterHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.build first
      apply bind_checked _ _ _ _ (buildMany_depth rest environment after afterContext afterHeap)
      intro values final completed finalHeap matched
      apply done_checked _ _ _ finalHeap
      simpa only [evaluateMany] using InternedOccurrenceObservations.Paired.cons observed matched
termination_by sizeOf expressions

/-- Actual surviving source edges have exactly the pure edge interpreter's maximum child depth. -/
theorem buildEdges_depth [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (buildEdges expressions environment state)
      (fun edges => maximumDepth ((surviving edges).flatMap EdgeValue.children) = (evaluateEdges expressions (environment.map shape)).depth) := by
  cases expressions with
  | nil =>
      rw [buildEdges, evaluateEdges]
      exact done_checked _ _ _ heap rfl
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have verified := buildMany_verified children _ state context.normal.facts context.inputs
          rw [buildEdges]
          apply bind_checked _ _ _ _ (buildMany_depth children environment state context heap)
          intro values after returned afterHeap matched
          have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many children
          have available := verified.result _ _ returned
          let actual := run (makeEdge symbol constraint values) after
          have edgeContext : Context actual.2 environment := afterContext.edge symbol constraint values available
          have edgeHeap : InternedFreshOrdinaryDepthHeap.Heap actual.2 := afterHeap
          have sameChildren : actual.1.children = values := InternedShallowValues.makeEdge_children symbol constraint values after
            afterContext.normal.facts.coherent afterContext.normal.facts.cached available
          simp only [work, Outcome.bind]
          change Checked ((buildEdges rest environment actual.2).bind _) _
          apply bind_checked _ _ _ _ (buildEdges_depth rest environment actual.2 edgeContext edgeHeap)
          intro edges final completed finalHeap same
          apply done_checked _ _ _ finalHeap
          rw [surviving_cons_depth, edge_depth actual.1 values _ sameChildren matched, same]
          simp only [evaluateEdges, combine]
termination_by sizeOf expressions
end

/-- Every normalized callback with captured records has its full syntax-derived observation. -/
theorem callback_depth [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (argument : Reference) (state : State Symbol Guard)
    (context : Context state environment) (available : Available state (.reference argument))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (callback body environment argument state)
      (fun value => value.depth = (symbolic body environment).depth ∧
        InternedFreshOrdinaryDepthHeap.Observed (captured body environment) (uses body environment) argument value) :=
  InternedRecordDepthCallback.callback_checked body environment argument state context available
    (build_depth body (.reference argument :: environment) state (context.local argument available) heap)

end MicroCFTA.InternedRecordDepthExecution
