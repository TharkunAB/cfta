import MicroCFTA.InternedFreshOrdinaryDepthComposition

/-!
# Actual nested source execution has the pure cached depth

The source induction retains the decoded depth heap through every outcome.
Completed results have the pure interpreter's depth and deep names. The
callback comparison uses actual probes and the fresh ordinary policy.
-/
namespace MicroCFTA.InternedFreshOrdinarySourceDepth
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryDepthComposition
open InternedFreshOrdinaryDepthRequest (Checked done_checked bind_checked)
open InternedDepthSemantics
open InternedDepthFreeProjectionSource (literal)
open InternedBinderProtocol (Reference)

mutual
/-- Full repaired source execution preserves the depth heap and derives each returned shape observation. -/
theorem build_depth [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (build expression (names.map Value.reference) state)
      (fun value => Observed value (evaluate expression (names.map literal))) := by
  cases expression with
  | empty =>
      rw [build, evaluate]
      exact done_checked _ _ _ heap ⟨rfl, rfl, by simp [InternedDeepFreeDepth.deepNames]⟩
  | var index =>
      rw [build]
      apply done_checked _ _ _ heap
      cases found : names[index]? with
      | none => simp only [evaluate, List.getElem?_map, found, Option.map_none, Option.getD_none]; exact ⟨rfl, rfl, by simp [InternedDeepFreeDepth.deepNames]⟩
      | some name =>
          simp only [evaluate, List.getElem?_map, found, Option.map_some, Option.getD_some]
          exact ⟨rfl, rfl, by simp [InternedDeepFreeDepth.deepNames, literal]⟩
  | node edges =>
      have verified := buildEdges_verified edges _ state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildEdges_depth edges names state context heap)
      intro values after returned afterHeap same
      have afterContext : Context after (names.map Value.reference) := by simpa only [returned, Outcome.state] using context.edges edges
      have available := verified.result _ _ returned
      have whole : build (.node edges) (names.map Value.reference) state =
          .done (run (makeNode values) after).1 (run (makeNode values) after).2 := by simp only [build, returned, Outcome.bind, work]
      apply done_checked
      · exact InternedFreshOrdinaryDepthHeap.preserve after _ afterHeap (InternedShallowHeap.makeNode_noNewMu values after)
      · exact ⟨source_empty _ names state context _ _ whole,
          (InternedNormalizationDepthExact.makeNode_surviving_depth values after afterContext.normal.facts.coherent
            afterContext.normal.facts.linked available).trans (by simpa only [evaluate] using same),
          InternedDepthFreeProjectionSource.node_deep edges names state context _ _ whole⟩
  | union members =>
      have verified := buildMany_verified members _ state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildMany_depth members names state context heap)
      intro values after returned afterHeap matched
      have afterContext : Context after (names.map Value.reference) := by simpa only [returned, Outcome.state] using context.many members
      apply done_checked
      · exact InternedFreshOrdinaryDepthHeap.preserve after _ afterHeap (InternedShallowHeap.makeUnion_noNewMu values after)
      · simpa only [evaluate] using union_observed values _ after afterContext (verified.result _ _ returned) matched
  | binder smart body =>
      have checked : ∀ argument current, Context current (names.map Value.reference) → Available current (.reference argument) →
          InternedFreshOrdinaryDepthHeap.Heap current →
          Checked (callback body (names.map Value.reference) argument current)
            (fun value => value.depth = (InternedDepthFreeProjectionCallback.symbolic body names).depth ∧
              InternedFreshOrdinaryDepthHeap.Observed (InternedDepthFreeProjectionCallback.captured body names)
                (InternedDepthFreeProjectionCallback.uses body names) argument value) := by
        intro argument current currentContext argumentAvailable currentHeap
        apply InternedFreshOrdinaryDepthComposition.callback_checked body names argument current currentContext argumentAvailable
        exact build_depth body (argument :: names) current (by simpa only [List.map_cons] using currentContext.local argument argumentAvailable) currentHeap
      have fullFree := InternedFreshOrdinaryFreeNames.build_free (.binder smart body) _ state context.normal context.inputs context.freeNames context.profiles
      rw [build]
      change Checked ((callback body (names.map Value.reference) .depth state).bind fun depth afterDepth =>
        (callback body (names.map Value.reference) (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body (names.map Value.reference)) afterOrdinary) _
      apply bind_checked _ _ _ _ (checked .depth state context (depth_available state) heap)
      intro depth afterDepth depthDone depthHeap depthObserved
      have depthContext : Context afterDepth (names.map Value.reference) := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
      have depthVerified := callback_verified body _ .depth state context.normal.facts (context.local .depth (depth_available state)).inputs
      have depthAvailable := depthVerified.result _ _ depthDone
      apply bind_checked _ _ _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext (ordinary_available afterDepth _) depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap ordinaryObserved
      have finalContext : Context afterOrdinary (names.map Value.reference) := by
        simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth _)
      have ordinaryVerified := callback_verified body _ (.uninterned (ordinaryLevel depth)) afterDepth
        depthContext.normal.facts (depthContext.local _ (ordinary_available afterDepth _)).inputs
      have finalDepth : Available afterOrdinary depth := by simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth depthAvailable
      have finalOrdinary := ordinaryVerified.result _ _ ordinaryDone
      have whole : build (.binder smart body) (names.map Value.reference) state =
          request smart depth ordinary (callback body (names.map Value.reference)) afterOrdinary := by
        rw [build]
        change ((callback body (names.map Value.reference) .depth state).bind _) = _
        rw [depthDone]
        change ((callback body (names.map Value.reference) (.uninterned (ordinaryLevel depth)) afterDepth).bind _) = _
        rw [ordinaryDone]
        rfl
      rw [whole] at fullFree
      have requested := InternedFreshOrdinaryDepthRequest.request_checked smart body _ depth ordinary afterOrdinary finalContext ordinaryHeap
        finalDepth finalOrdinary _ _ _ depthObserved.1 depthObserved.2 ordinaryObserved.2 fullFree.heap
        (fun argument current currentContext argumentAvailable currentHeap => checked argument current currentContext argumentAvailable currentHeap)
      have decoded := binder_decoded smart body names depth ordinary afterOrdinary finalContext finalDepth depthObserved.1
        depthObserved.2 ordinaryObserved.2
        (callback_free body names .depth state context (depth_available state) depth afterDepth depthDone)
        (callback_free body names (.uninterned (ordinaryLevel depth)) afterDepth depthContext (ordinary_available afterDepth _) ordinary afterOrdinary ordinaryDone)
      refine ⟨requested.heap, ?_⟩
      intro value after returned
      have observed := requested.result _ _ returned
      exact ⟨source_empty _ names state context _ _ (whole.trans returned), observed.1.trans decoded.1,
        fun name => (observed.2 name).trans (decoded.2 name)⟩
termination_by sizeOf expression

/-- Ordered source children retain their pure shape observations at every position. -/
theorem buildMany_depth [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (buildMany expressions (names.map Value.reference) state)
      (fun values => Matches values (evaluateMany expressions (names.map literal))) := by
  cases expressions with
  | nil =>
      rw [buildMany, evaluateMany]
      exact done_checked _ _ _ heap .nil
  | cons first rest =>
      rw [buildMany]
      apply bind_checked _ _ _ _ (build_depth first names state context heap)
      intro value after returned afterHeap observed
      have afterContext : Context after (names.map Value.reference) := by simpa only [returned, Outcome.state] using context.build first
      apply bind_checked _ _ _ _ (buildMany_depth rest names after afterContext afterHeap)
      intro values final completed finalHeap matched
      apply done_checked _ _ _ finalHeap
      simpa only [evaluateMany] using InternedOccurrenceObservations.Paired.cons observed matched
termination_by sizeOf expressions

/-- Actual surviving source edges have exactly the pure edge interpreter's maximum child depth. -/
theorem buildEdges_depth [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (buildEdges expressions (names.map Value.reference) state)
      (fun edges => maximumDepth ((surviving edges).flatMap EdgeValue.children) = (evaluateEdges expressions (names.map literal)).depth) := by
  cases expressions with
  | nil =>
      rw [buildEdges, evaluateEdges]
      exact done_checked _ _ _ heap rfl
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have verified := buildMany_verified children _ state context.normal.facts context.inputs
          rw [buildEdges]
          apply bind_checked _ _ _ _ (buildMany_depth children names state context heap)
          intro values after returned afterHeap matched
          have afterContext : Context after (names.map Value.reference) := by simpa only [returned, Outcome.state] using context.many children
          have available := verified.result _ _ returned
          let actual := run (makeEdge symbol constraint values) after
          have edgeContext : Context actual.2 (names.map Value.reference) := afterContext.edge symbol constraint values available
          have edgeHeap : InternedFreshOrdinaryDepthHeap.Heap actual.2 := afterHeap
          have sameChildren : actual.1.children = values := InternedShallowValues.makeEdge_children symbol constraint values after
            afterContext.normal.facts.coherent afterContext.normal.facts.cached available
          simp only [work, Outcome.bind]
          change Checked ((buildEdges rest (names.map Value.reference) actual.2).bind _) _
          apply bind_checked _ _ _ _ (buildEdges_depth rest names actual.2 edgeContext edgeHeap)
          intro edges final completed finalHeap same
          apply done_checked _ _ _ finalHeap
          rw [surviving_cons_depth, edge_depth actual.1 values _ sameChildren matched, same]
          simp only [evaluateEdges, combine]
termination_by sizeOf expressions
end

/-- Every actual normalized callback has its syntax-derived depth and complete deep-name response. -/
theorem callback_depth [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (names : List Reference) (argument : Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (available : Available state (.reference argument))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (callback body (names.map Value.reference) argument state)
      (fun value => value.depth = (InternedDepthFreeProjectionCallback.symbolic body names).depth ∧
        InternedFreshOrdinaryDepthHeap.Observed (InternedDepthFreeProjectionCallback.captured body names)
          (InternedDepthFreeProjectionCallback.uses body names) argument value) :=
  InternedFreshOrdinaryDepthComposition.callback_checked body names argument state context available
    (build_depth body (argument :: names) state (by simpa only [List.map_cons] using context.local argument available) heap)

/-- Two actual completed callbacks with the same literal captures have identical cached depth for any supplied names. -/
theorem arguments_depth [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (names : List Reference) (firstName secondName : Reference) (firstState secondState : State Symbol Guard)
    (firstContext : Context firstState (names.map Value.reference)) (secondContext : Context secondState (names.map Value.reference))
    (firstAvailable : Available firstState (.reference firstName)) (secondAvailable : Available secondState (.reference secondName))
    (firstHeap : InternedFreshOrdinaryDepthHeap.Heap firstState) (secondHeap : InternedFreshOrdinaryDepthHeap.Heap secondState)
    (first second : Value Symbol Guard) (afterFirst afterSecond : State Symbol Guard)
    (firstDone : callback body (names.map Value.reference) firstName firstState = .done first afterFirst)
    (secondDone : callback body (names.map Value.reference) secondName secondState = .done second afterSecond) : first.depth = second.depth :=
  ((callback_depth body names firstName firstState firstContext firstAvailable firstHeap).result _ _ firstDone).1.trans
    ((callback_depth body names secondName secondState secondContext secondAvailable secondHeap).result _ _ secondDone).1.symm

/-- Every closed source execution derives the decoded heap, including when its outcome is pending. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    InternedFreshOrdinaryDepthHeap.Heap (build expression [] empty).state :=
  (build_depth expression [] empty InternedFreshOrdinaryContext.empty_context InternedFreshOrdinaryDepthHeap.empty_heap).heap

/-- A completed closed source expression has exactly the independent pure depth and deep names. -/
theorem closed_observed [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard) (done : build expression [] empty = .done value state) :
    Observed value (evaluate expression []) :=
  (build_depth expression [] empty InternedFreshOrdinaryContext.empty_context InternedFreshOrdinaryDepthHeap.empty_heap).result value state done

end MicroCFTA.InternedFreshOrdinarySourceDepth
