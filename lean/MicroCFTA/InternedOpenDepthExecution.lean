import MicroCFTA.InternedOpenDepthRequest
import MicroCFTA.InternedRecordDepthExecution

/-!
# Open-depth correspondence for actual repaired source execution

The source induction follows both probes, the fresh body, and canonical
readback. It retains the actual final cache and proves body/probe open-depth
equality for each complete Mu. The initial open-depth heap is explicit.
-/
namespace MicroCFTA.InternedOpenDepthExecution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedOpenDepthReadback InternedOpenDepthRequest InternedStoredPlanBinderDepth
open InternedRecordDepthShape (shape)
open InternedRecordDepthCallback (symbolic captured uses)
open InternedBinderProtocol (Reference)

/-- Lists with equal membership have the same empty decision. -/
theorem isEmpty_of_membership (first second : List Atom) (same : ∀ atom, atom ∈ first ↔ atom ∈ second) :
    first.isEmpty = second.isEmpty := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.isEmpty_iff]
  constructor
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro atom member
    have impossible := (same atom).mpr member
    simp [empty] at impossible
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro atom member
    have impossible := (same atom).mp member
    simp [empty] at impossible

/-- Source edge deletion uses the original child empty decision and exact open-depth maximum. -/
theorem surviving_cons (edge : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    edgesDepth (surviving (edge :: rest)) =
      max (if edge.children.any (fun child => child.referenceOf == .empty) then 0 else manyDepth edge.children)
        (edgesDepth (surviving rest)) := by
  cases alive : edge.children.any (fun child => child.referenceOf == .empty) <;>
    cases edge <;> simp_all [surviving, edgesDepth, EdgeValue.children]

mutual
/-- Actual repaired source execution retains its open-depth heap and exact interpreted result depth. -/
theorem build_depth [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : Heap state) :
    Checked (build expression environment state)
      (fun value => valueDepth value = InternedOpenDepthSemantics.evaluate expression
        (environment.map shape) (environment.map valueDepth)) := by
  cases expression with
  | empty =>
      rw [build, InternedOpenDepthSemantics.evaluate]
      exact done_checked _ _ _ heap (by simp [valueDepth, Value.free])
  | var index =>
      rw [build]
      apply done_checked _ _ _ heap
      cases found : environment[index]? with
      | none => simp [InternedOpenDepthSemantics.evaluate, List.getElem?_map, found, valueDepth, Value.free]
      | some value => simp only [InternedOpenDepthSemantics.evaluate, List.getElem?_map, found, Option.map_some, Option.getD_some]
  | node edges =>
      have verified := buildEdges_verified edges environment state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildEdges_depth edges environment state context cached heap)
      intro values after returned afterHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.edges edges
      apply done_checked
      · exact preserve after _ afterHeap (InternedShallowHeap.makeNode_noNewMu values after)
      · rw [InternedOpenDepthSemantics.evaluate]
        exact (makeNode_depth values after afterContext.normal.facts.coherent afterContext.normal.facts.linked
          (verified.result values after returned)).trans observed
  | union members =>
      have verified := buildMany_verified members environment state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildMany_depth members environment state context cached heap)
      intro values after returned afterHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many members
      apply done_checked
      · exact preserve after _ afterHeap (InternedShallowHeap.makeUnion_noNewMu values after)
      · rw [InternedOpenDepthSemantics.evaluate]
        exact (makeUnion_depth values after afterContext.normal.facts.coherent afterContext.normal.facts.cached
          afterContext.normal.facts.linked afterContext.normal.live (verified.result values after returned)).trans observed
  | binder smart body =>
      let expected := InternedOpenDepthSemantics.evaluate body
        (⟨[Sum.inl ()], [], false, 0⟩ :: (environment.map shape).map (InternedDepthSemantics.Shape.map Sum.inr))
        (0 :: environment.map valueDepth)
      have checked : ∀ argument current, Context current environment → Available current (.reference argument) →
          InternedFreshOrdinaryDepthHeap.Heap current → Heap current →
          Checked (callback body environment argument current) (fun value => valueDepth value = expected) := by
        intro argument current currentContext argumentAvailable currentCached currentHeap
        have localContext := currentContext.local argument argumentAvailable
        have verified := InternedFreshOrdinaryFacts.build_verified body _ current localContext.normal.facts localContext.inputs
        unfold callback
        apply bind_checked _ _ _ _ (build_depth body (.reference argument :: environment) current localContext currentCached currentHeap)
        intro value after returned afterHeap observed
        have afterContext : Context after (.reference argument :: environment) := by
          simpa only [returned, Outcome.state] using localContext.build body
        apply done_checked
        · exact preserve after _ afterHeap (InternedStoredMuOrigins.filter_noNewMu argument value after)
        · have actual := filter_depth argument value after afterContext.normal.facts.coherent afterContext.normal.facts.cached
            afterContext.normal.facts.linked afterContext.normal.live (verified.result value after returned)
          have referenceZero : valueDepth (Value.reference argument : Value Symbol Guard) = 0 := by simp [valueDepth, Value.free]
          simp only [List.map_cons, shape] at observed
          rw [referenceZero] at observed
          exact actual.trans (observed.trans (InternedOpenDepthSemantics.supplied_depth body
            (environment.map shape) (environment.map valueDepth) argument))
      have depthOld := InternedRecordDepthExecution.callback_depth body environment .depth state context (depth_available state) cached
      have depthVerified := callback_verified body environment .depth state context.normal.facts
        (context.local .depth (depth_available state)).inputs
      have wholeOld := InternedRecordDepthExecution.build_depth (.binder smart body) environment state context cached
      rw [build]
      change Checked ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary) _
      apply bind_checked _ _ _ _ (checked .depth state context (depth_available state) cached heap)
      intro depth afterDepth depthDone depthHeap depthExpected
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
      have depthCached : InternedFreshOrdinaryDepthHeap.Heap afterDepth := by simpa only [depthDone, Outcome.state] using depthOld.heap
      have depthObserved := (depthOld.result depth afterDepth depthDone).2
      have depthAvailable := depthVerified.result depth afterDepth depthDone
      have ordinaryOld := InternedRecordDepthExecution.callback_depth body environment (.uninterned (ordinaryLevel depth))
        afterDepth depthContext (ordinary_available afterDepth _) depthCached
      have ordinaryVerified := callback_verified body environment (.uninterned (ordinaryLevel depth)) afterDepth
        depthContext.normal.facts (depthContext.local _ (ordinary_available afterDepth _)).inputs
      apply bind_checked _ _ _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available afterDepth _) depthCached depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap ordinaryExpected
      have finalContext : Context afterOrdinary environment := by
        simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth _)
      have finalCached : InternedFreshOrdinaryDepthHeap.Heap afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryOld.heap
      have finalDepth : Available afterOrdinary depth := by simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth depthAvailable
      have finalOrdinary := ordinaryVerified.result ordinary afterOrdinary ordinaryDone
      have ordinaryObserved := (ordinaryOld.result ordinary afterOrdinary ordinaryDone).2
      have whole : build (.binder smart body) environment state =
          request smart depth ordinary (callback body environment) afterOrdinary := by
        rw [build]
        change ((callback body environment .depth state).bind _) = _
        rw [depthDone]
        change ((callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind _) = _
        rw [ordinaryDone]
        rfl
      have retained := request_heap smart body environment depth ordinary afterOrdinary finalContext finalCached
        ordinaryHeap expected depthExpected (fun argument current ctx available old now => checked argument current ctx available old now)
      refine ⟨retained, ?_⟩
      intro value after returned
      have afterHeap : Heap after := by simpa only [returned, Outcome.state] using retained
      have afterCached : InternedFreshOrdinaryDepthHeap.Heap after := by simpa only [whole, returned, Outcome.state] using wholeOld.heap
      have readback := request_depth smart body environment depth ordinary afterOrdinary finalContext.normal.facts finalDepth
        finalOrdinary value after returned afterHeap afterCached
      have freeEmpty : value.free.isEmpty = (InternedDepthSemantics.binder smart (symbolic body environment)).free.isEmpty := by
        apply isEmpty_of_membership
        intro name
        simpa only [InternedDepthSemantics.evaluate, symbolic] using
          InternedRecordDepthSource.source_free (.binder smart body) environment state context value after (whole.trans returned) name
      have fresh : .uninterned (ordinaryLevel depth) ∉ captured body environment := by
        intro member
        have present := (InternedFreshOrdinaryDepthHeap.observed_other _ _ .depth depth depthObserved
          (.uninterned (ordinaryLevel depth)) (by intro impossible; cases impossible)).mpr member
        exact ordinary_fresh depth (InternedDeepFreeNormalization.deep_free depth afterDepth
          depthContext.normal.facts.coherent depthAvailable _ present)
      have own := InternedFreshOrdinaryDepthHeap.observed_own _ _ (.uninterned (ordinaryLevel depth)) ordinary ordinaryObserved fresh
      have useExact : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = InternedDepthSemantics.hasLocal (symbolic body environment).deep := by
        rw [InternedFreshOrdinaryDepthComposition.hasLocal_uses]
        apply Bool.eq_iff_iff.mpr
        simpa only [InternedFreshOrdinaryDepthHeap.usesLocal, decide_eq_true_eq, uses] using own
      rw [InternedOpenDepthSemantics.evaluate]
      change valueDepth value = InternedOpenDepthSemantics.binderDepth smart (symbolic body environment) expected
      rw [readback, freeEmpty, useExact, depthExpected]
      rfl
termination_by sizeOf expression

/-- Ordered source children retain their exact maximum interpreted open depth. -/
theorem buildMany_depth [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : Heap state) :
    Checked (buildMany expressions environment state)
      (fun values => manyDepth values = InternedOpenDepthSemantics.evaluateMany expressions
        (environment.map shape) (environment.map valueDepth)) := by
  cases expressions with
  | nil =>
      rw [buildMany, InternedOpenDepthSemantics.evaluateMany]
      exact done_checked _ _ _ heap (by rw [manyDepth])
  | cons first rest =>
      have old := InternedRecordDepthExecution.build_depth first environment state context cached
      rw [buildMany]
      apply bind_checked _ _ _ _ (build_depth first environment state context cached heap)
      intro value after returned afterHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.build first
      have afterCached : InternedFreshOrdinaryDepthHeap.Heap after := by simpa only [returned, Outcome.state] using old.heap
      apply bind_checked _ _ _ _ (buildMany_depth rest environment after afterContext afterCached afterHeap)
      intro values final completed finalHeap matched
      apply done_checked _ _ _ finalHeap
      rw [manyDepth, observed, matched, InternedOpenDepthSemantics.evaluateMany]
termination_by sizeOf expressions

/-- Actual source edges retain their interpreted surviving open-depth maximum. -/
theorem buildEdges_depth [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : Heap state) :
    Checked (buildEdges expressions environment state)
      (fun edges => edgesDepth (surviving edges) = InternedOpenDepthSemantics.evaluateEdges expressions
        (environment.map shape) (environment.map valueDepth)) := by
  cases expressions with
  | nil =>
      rw [buildEdges, InternedOpenDepthSemantics.evaluateEdges]
      exact done_checked _ _ _ heap (by simp [edgesDepth, surviving])
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have verified := buildMany_verified children environment state context.normal.facts context.inputs
          have old := InternedRecordDepthExecution.buildMany_depth children environment state context cached
          rw [buildEdges]
          apply bind_checked _ _ _ _ (buildMany_depth children environment state context cached heap)
          intro values after returned afterHeap observed
          have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many children
          have afterCached : InternedFreshOrdinaryDepthHeap.Heap after := by simpa only [returned, Outcome.state] using old.heap
          have available := verified.result values after returned
          let actual := run (makeEdge symbol constraint values) after
          have edgeContext : Context actual.2 environment := afterContext.edge symbol constraint values available
          have sameChildren : actual.1.children = values := InternedShallowValues.makeEdge_children symbol constraint values after
            afterContext.normal.facts.coherent afterContext.normal.facts.cached available
          have emptyExact := InternedFreshOrdinaryDepthComposition.children_empty (old.result values after returned)
          simp only [work, Outcome.bind]
          change Checked ((buildEdges rest environment actual.2).bind _) _
          apply bind_checked _ _ _ _ (buildEdges_depth rest environment actual.2 edgeContext afterCached afterHeap)
          intro edges final completed finalHeap same
          apply done_checked _ _ _ finalHeap
          rw [surviving_cons, sameChildren, emptyExact, observed, same]
          rw [InternedOpenDepthSemantics.evaluateEdges]
termination_by sizeOf expressions
end

/-- Each actual normalized callback retains its exact symbolic open-depth observation. -/
theorem callback_depth [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (argument : Reference) (state : State Symbol Guard)
    (context : Context state environment) (available : Available state (.reference argument))
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : Heap state) :
    Checked (callback body environment argument state)
      (fun value => valueDepth value = InternedOpenDepthSemantics.evaluate body
        (⟨[Sum.inl ()], [], false, 0⟩ :: (environment.map shape).map (InternedDepthSemantics.Shape.map Sum.inr))
        (0 :: environment.map valueDepth)) := by
  have localContext := context.local argument available
  have verified := InternedFreshOrdinaryFacts.build_verified body _ state localContext.normal.facts localContext.inputs
  unfold callback
  apply bind_checked _ _ _ _ (build_depth body (.reference argument :: environment) state localContext cached heap)
  intro value after returned afterHeap observed
  have afterContext : Context after (.reference argument :: environment) := by
    simpa only [returned, Outcome.state] using localContext.build body
  apply done_checked
  · exact preserve after _ afterHeap (InternedStoredMuOrigins.filter_noNewMu argument value after)
  · have actual := filter_depth argument value after afterContext.normal.facts.coherent afterContext.normal.facts.cached
      afterContext.normal.facts.linked afterContext.normal.live (verified.result value after returned)
    have referenceZero : valueDepth (Value.reference argument : Value Symbol Guard) = 0 := by simp [valueDepth, Value.free]
    simp only [List.map_cons, shape] at observed
    rw [referenceZero] at observed
    exact actual.trans (observed.trans (InternedOpenDepthSemantics.supplied_depth body
      (environment.map shape) (environment.map valueDepth) argument))

/-- Every actual source cache built from empty has body/Depth-probe open-depth equality. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap (build expression [] (empty (Symbol := Symbol) (Guard := Guard))).state :=
  (build_depth expression [] empty empty_context InternedFreshOrdinaryDepthHeap.empty_heap empty_heap).heap

/-- Each complete Mu from actual empty-cache construction has equal body and Depth-probe open depth. -/
theorem closed_probe_equal [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    valueDepth body = valueDepth depth :=
  closed_heap expression key entry body depth ordinary present

/-- Actual completed source results satisfy their static binder-depth and lexical-input bound. -/
theorem build_bound [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : Heap state)
    (bound : Nat) (inputs : ∀ value ∈ environment, valueDepth value ≤ bound)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build expression environment state = .done value after) :
    valueDepth value ≤ syntaxDepth expression + bound := by
  rw [(build_depth expression environment state context cached heap).result value after done]
  apply InternedOpenDepthSemantics.evaluate_bound
  intro depth member
  obtain ⟨value, included, rfl⟩ := List.mem_map.mp member
  exact inputs value included

/-- Actual completed normalized callbacks retain the source-body and lexical-input open-depth bound. -/
theorem callback_bound [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (argument : Reference) (state : State Symbol Guard)
    (context : Context state environment) (available : Available state (.reference argument))
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : Heap state)
    (bound : Nat) (inputs : ∀ value ∈ environment, valueDepth value ≤ bound)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : callback body environment argument state = .done value after) :
    valueDepth value ≤ syntaxDepth body + bound := by
  rw [(callback_depth body environment argument state context available cached heap).result value after done]
  apply InternedOpenDepthSemantics.evaluate_bound
  intro depth member
  rcases List.mem_cons.mp member with rfl | included
  · exact Nat.zero_le _
  · obtain ⟨original, originalIncluded, equal⟩ := List.mem_map.mp included
    rw [← equal]
    exact inputs original originalIncluded

end MicroCFTA.InternedOpenDepthExecution
