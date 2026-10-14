import MicroCFTA.InternedGuardedBudgetExecutionLists

/-!
# Exact unfolding budgets of actual repaired source execution

The source induction follows both probes, fresh completion, and canonical
hits. It derives raw-Mu and empty-local probe readback together with each
returned budget language. The existing depth heap decides smart cleanup.
-/
namespace MicroCFTA.InternedGuardedBudgetExecution
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedGuardedBudget InternedGuardedBudgetProbeHeap InternedGuardedBudgetRequest InternedGuardedBudgetExecutionLists
open InternedBinderProtocol (Reference)
open BinderBudgetLanguage (Lang)
open InternedRecordDepthShape (shape)
open InternedGuardedExecutionLists (exists_member exists_cons)
open InternedGuardedBudgetCallback (bodyMeaning)

mutual
/-- Actual repaired execution retains both probe heaps and returns the exact smart budget language. -/
theorem build_language [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (build expression environment state) (fun value => ∀ holds ambient,
      meaning holds ambient value = InternedGuardedSmartBudget.evaluate holds (environment.map shape) (environment.map (meaning holds ambient)) expression) := by
  cases expression with
  | empty =>
      rw [build]
      exact done_checked _ _ _ heap depthHeap (by intro holds ambient; rw [meaning, InternedGuardedSmartBudget.evaluate])
  | var index =>
      rw [build]
      apply done_checked _ _ _ heap depthHeap
      intro holds ambient
      rw [InternedGuardedSmartBudget.evaluate]
      cases found : environment[index]? with
      | none => simp only [found, Option.getD_none, List.getElem?_map, Option.map_none, meaning]
      | some value => simp only [found, Option.getD_some, List.getElem?_map, Option.map_some]
  | node edges =>
      have verified := buildEdges_verified edges environment state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildEdges_language edges environment state context heap depthHeap)
      intro values after returned afterHeap afterDepthHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.edges edges
      apply done_checked
      · exact preserve after _ afterHeap (InternedShallowHeap.makeNode_noNewMu values after)
      · exact InternedFreshOrdinaryDepthHeap.preserve after _ afterDepthHeap (InternedShallowHeap.makeNode_noNewMu values after)
      · intro holds ambient
        funext budget term
        apply propext
        have normalized := makeNode_exact after afterContext.normal.facts holds ambient values (verified.result values after returned) budget term
        have ordinary : meaning holds ambient (run (makeNode values) after).1 budget term ↔
            ∃ edge ∈ values, edgeMeaning holds ambient edge budget term := by
          simpa only [← edgeMeaning_all] using normalized
        rw [InternedGuardedSmartBudget.evaluate]
        exact ordinary.trans ((observed holds ambient budget term).trans (exists_member _ _).symm)
  | union members =>
      have verified := buildMany_verified members environment state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildMany_language members environment state context heap depthHeap)
      intro values after returned afterHeap afterDepthHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many members
      apply done_checked
      · exact preserve after _ afterHeap (InternedShallowHeap.makeUnion_noNewMu values after)
      · exact InternedFreshOrdinaryDepthHeap.preserve after _ afterDepthHeap (InternedShallowHeap.makeUnion_noNewMu values after)
      · intro holds ambient
        funext budget term
        apply propext
        rw [InternedGuardedSmartBudget.evaluate]
        exact (makeUnion_exact after afterContext.normal.facts holds ambient values (verified.result values after returned) budget term).trans
          ((alternatives_equal values members _ _ (observed holds ambient) budget term).trans (exists_member _ _).symm)
  | binder smart body =>
      let expected := fun holds ambient => bodyMeaning holds ambient body environment
      have checked : ∀ argument current, Context current environment → Available current (.reference argument) →
          Heap current → InternedFreshOrdinaryDepthHeap.Heap current →
          Checked (callback body environment argument current) (fun value => ∀ holds ambient,
            argument ∉ InternedProfileCallbackForm.captures
              (InternedFreeNameForm.symbolic body (environment.map InternedRootProfile.profile) (environment.map Value.free)) →
            InternedGuardedBudgetCallback.View holds ambient argument value (expected holds ambient)) := by
        intro argument current currentContext argumentAvailable currentHeap currentDepthHeap
        have localContext := currentContext.local argument argumentAvailable
        have verified := build_verified body _ current localContext.normal.facts localContext.inputs
        unfold callback
        apply bind_checked _ _ _ _ (build_language body (.reference argument :: environment) current localContext currentHeap currentDepthHeap)
        intro value after returned afterHeap afterDepthHeap observed
        have afterContext : Context after (.reference argument :: environment) := by
          simpa only [returned, Outcome.state] using localContext.build body
        have capturesContext : Context after environment :=
          ⟨afterContext.normal, fun value member => afterContext.inputs value (List.mem_cons_of_mem _ member),
            afterContext.profiles, afterContext.freeNames⟩
        apply done_checked
        · exact preserve after _ afterHeap (InternedStoredMuOrigins.filter_noNewMu argument value after)
        · exact InternedFreshOrdinaryDepthHeap.preserve after _ afterDepthHeap (InternedStoredMuOrigins.filter_noNewMu argument value after)
        · intro holds ambient fresh
          exact InternedGuardedBudgetCallback.filter_view body environment argument value after capturesContext
            (verified.result value after returned) observed fresh holds ambient
      have depthVerified := callback_verified body environment .depth state context.normal.facts
        (context.local .depth (depth_available state)).inputs
      have wholeVerified := build_verified (.binder smart body) environment state context.normal.facts context.inputs
      have wholeDepth := InternedRecordDepthExecution.build_depth (.binder smart body) environment state context depthHeap
      rw [build]
      change Checked ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary) _
      apply bind_checked _ _ _ _ (checked .depth state context (depth_available state) heap depthHeap)
      intro depth afterDepth depthDone depthHeapBudget depthHeapOld _
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
      have depthAvailable := depthVerified.result depth afterDepth depthDone
      have fresh := InternedGuardedProbeHeap.ordinary_fresh_captures body environment state context depth afterDepth depthDone
      have ordinaryVerified := callback_verified body environment (.uninterned (ordinaryLevel depth)) afterDepth
        depthContext.normal.facts (depthContext.local _ (ordinary_available afterDepth _)).inputs
      have ordinaryShape := InternedRecordDepthExecution.callback_depth body environment (.uninterned (ordinaryLevel depth))
        afterDepth depthContext (ordinary_available afterDepth _) depthHeapOld
      apply bind_checked _ _ _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available afterDepth _) depthHeapBudget depthHeapOld)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap ordinaryDepthHeap ordinaryObserved
      have finalContext : Context afterOrdinary environment := by
        simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth _)
      have finalDepth : Available afterOrdinary depth := by
        simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth depthAvailable
      have finalOrdinary := ordinaryVerified.result ordinary afterOrdinary ordinaryDone
      have ordinaryExpected : ∀ holds ambient, InternedGuardedBudgetCallback.View holds ambient
          (.uninterned (ordinaryLevel depth)) ordinary (expected holds ambient) :=
        fun holds ambient => ordinaryObserved holds ambient fresh
      have usesSame := InternedGuardedBudgetCallback.uses_source body environment depth ordinary afterOrdinary finalContext fresh
        (ordinaryShape.result ordinary afterOrdinary ordinaryDone).2
      have retained := request_heap smart body environment depth ordinary afterOrdinary finalContext ordinaryHeap ordinaryDepthHeap
        expected ordinaryExpected (fun argument current ctx available currentHeap currentDepthHeap fresh =>
          ⟨(checked argument current ctx available currentHeap currentDepthHeap).heap,
            (checked argument current ctx available currentHeap currentDepthHeap).depthHeap,
            fun value after returned holds ambient =>
              (checked argument current ctx available currentHeap currentDepthHeap).result value after returned holds ambient fresh⟩)
      have whole : build (.binder smart body) environment state =
          request smart depth ordinary (callback body environment) afterOrdinary := by
        rw [build]
        change ((callback body environment .depth state).bind _) = _
        rw [depthDone]
        change ((callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind _) = _
        rw [ordinaryDone]
        rfl
      have retainedDepth : InternedFreshOrdinaryDepthHeap.Heap
          (request smart depth ordinary (callback body environment) afterOrdinary).state := by
        simpa only [whole] using wholeDepth.heap
      refine ⟨retained, retainedDepth, ?_⟩
      intro value after returned holds ambient
      have afterHeap : Heap after := by simpa only [returned, Outcome.state] using retained
      have afterDepthHeap : InternedFreshOrdinaryDepthHeap.Heap after := by simpa only [returned, Outcome.state] using retainedDepth
      have afterFacts : InternedNestedFacts.Facts after := by
        simpa only [whole, returned, Outcome.state] using wholeVerified.facts
      rw [InternedGuardedSmartBudget.evaluate]
      change meaning holds ambient value =
        if !smart || InternedDepthSemantics.hasLocal (InternedRecordDepthCallback.symbolic body environment).deep then
          BinderBudgetLanguage.mu (expected holds ambient) else expected holds ambient (fun _ _ => False)
      rw [request_language holds ambient smart body environment depth ordinary afterOrdinary finalContext.normal.facts
        finalDepth finalOrdinary value after returned afterFacts afterHeap afterDepthHeap, usesSame]
      split
      · exact (ordinaryExpected holds ambient).1
      · exact (ordinaryExpected holds ambient).2

termination_by sizeOf expression

/-- Ordered actual child execution retains the exact ordered budget-language list. -/
theorem buildMany_language [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (buildMany expressions environment state) (fun values => ∀ holds ambient,
      values.map (meaning holds ambient) = expressions.map (InternedGuardedSmartBudget.evaluate holds (environment.map shape) (environment.map (meaning holds ambient)))) := by
  cases expressions with
  | nil =>
      rw [buildMany]
      exact done_checked _ _ _ heap depthHeap (by intro holds ambient; rfl)
  | cons first rest =>
      rw [buildMany]
      apply bind_checked _ _ _ _ (build_language first environment state context heap depthHeap)
      intro value after returned afterHeap afterDepthHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.build first
      apply bind_checked _ _ _ _ (buildMany_language rest environment after afterContext afterHeap afterDepthHeap)
      intro values final completed finalHeap finalDepthHeap matched
      apply done_checked _ _ _ finalHeap finalDepthHeap
      intro holds ambient
      rw [List.map_cons, List.map_cons, observed holds ambient, matched holds ambient]
termination_by sizeOf expressions

/-- Actual source edge execution retains full guards, child order, and fixed-budget alternatives. -/
theorem buildEdges_language [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (buildEdges expressions environment state) (fun values => ∀ holds ambient budget term,
      (∃ edge ∈ values, edgeMeaning holds ambient edge budget term) ↔
        ∃ edge ∈ expressions, InternedGuardedSmartBudget.edgeMeaning holds (environment.map shape) (environment.map (meaning holds ambient)) edge budget term) := by
  cases expressions with
  | nil =>
      rw [buildEdges]
      exact done_checked _ _ _ heap depthHeap (by intro holds ambient budget term; simp only [List.not_mem_nil, false_and, exists_false])
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          have verified := buildMany_verified children environment state context.normal.facts context.inputs
          rw [buildEdges]
          apply bind_checked _ _ _ _ (buildMany_language children environment state context heap depthHeap)
          intro values after returned afterHeap afterDepthHeap observed
          have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many children
          have available := verified.result values after returned
          let actual := run (makeEdge symbol guard values) after
          have edgeContext : Context actual.2 environment := afterContext.edge symbol guard values available
          have headSame := fun holds ambient => makeEdge_language holds ambient (environment.map shape) (environment.map (meaning holds ambient)) symbol guard values children
            after afterContext.normal.facts.coherent afterContext.normal.facts.cached available (observed holds ambient)
          simp only [work, Outcome.bind]
          change Checked ((buildEdges rest environment actual.2).bind _) _
          apply bind_checked _ _ _ _ (buildEdges_language rest environment actual.2 edgeContext afterHeap afterDepthHeap)
          intro edges final completed finalHeap finalDepthHeap matched
          apply done_checked _ _ _ finalHeap finalDepthHeap
          intro holds ambient budget term
          rw [exists_cons, exists_cons]
          exact or_congr (iff_of_eq (congrFun (congrFun (headSame holds ambient) budget) term)) (matched holds ambient budget term)
termination_by sizeOf expressions
end

/-- A completed closed source plan has exactly its intended smart unfolding budgets. -/
theorem closed_language [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (done : build expression [] empty = .done value state) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) :
    meaning holds ambient value = InternedGuardedSmartBudget.evaluate holds ([] : List (InternedDepthSemantics.Shape Reference)) [] expression :=
  (build_language expression [] empty empty_context empty_heap InternedFreshOrdinaryDepthHeap.empty_heap).result value state done holds ambient

/-- Complete and pending closed executions retain both ordinary-probe budget readbacks. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap (build expression [] empty).state :=
  (build_language expression [] empty empty_context empty_heap InternedFreshOrdinaryDepthHeap.empty_heap).heap

end MicroCFTA.InternedGuardedBudgetExecution
