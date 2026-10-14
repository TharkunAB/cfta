import MicroCFTA.InternedGuardedExecutionLists

/-!
# Independent guarded language of actual repaired source execution

The source induction follows both probes, fresh completion, and canonical
hits. It derives the semantic probe heap together with each returned
language. Every statement retains the exact completed or pending cache.
-/
namespace MicroCFTA.InternedGuardedExecution
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedGuardedLanguage InternedGuardedProbeHeap InternedGuardedRequest InternedGuardedExecutionLists
open InternedBinderProtocol (Reference)
open BinderLanguage (Lang least)

mutual
/-- Actual repaired execution preserves the semantic probe heap and returns the independent source-plan language. -/
theorem build_language [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) :
    Checked (build expression environment state) (fun value => ∀ holds ambient,
      meaning holds ambient value = InternedGuardedSyntax.evaluate holds (environment.map (meaning holds ambient)) expression) := by
  cases expression with
  | empty =>
      rw [build]
      exact done_checked _ _ _ heap (by intro holds ambient; rw [meaning, InternedGuardedSyntax.evaluate])
  | var index =>
      rw [build]
      apply done_checked _ _ _ heap
      intro holds ambient
      rw [InternedGuardedSyntax.evaluate]
      cases found : environment[index]? with
      | none => simp only [found, Option.getD_none, List.getElem?_map, Option.map_none, meaning]
      | some value => simp only [found, Option.getD_some, List.getElem?_map, Option.map_some]
  | node edges =>
      have verified := buildEdges_verified edges environment state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildEdges_language edges environment state context heap)
      intro values after returned afterHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.edges edges
      apply done_checked
      · exact preserve after _ afterHeap (InternedShallowHeap.makeNode_noNewMu values after)
      · intro holds ambient
        funext term
        apply propext
        have normalized := makeNode_exact after afterContext.normal.facts holds ambient values (verified.result values after returned) term
        have ordinary : meaning holds ambient (run (makeNode values) after).1 term ↔
            ∃ edge ∈ values, edgeMeaning holds ambient edge term := by
          simpa only [← edgeMeaning_all] using normalized
        rw [InternedGuardedSyntax.evaluate]
        exact ordinary.trans ((observed holds ambient term).trans (exists_member _ _).symm)
  | union members =>
      have verified := buildMany_verified members environment state context.normal.facts context.inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildMany_language members environment state context heap)
      intro values after returned afterHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many members
      apply done_checked
      · exact preserve after _ afterHeap (InternedShallowHeap.makeUnion_noNewMu values after)
      · intro holds ambient
        funext term
        apply propext
        rw [InternedGuardedSyntax.evaluate]
        exact (makeUnion_exact after afterContext.normal.facts holds ambient values (verified.result values after returned) term).trans
          ((alternatives_equal values members _ _ (observed holds ambient) term).trans (exists_member _ _).symm)
  | binder smart body =>
      let expected := fun (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) =>
        least (fun language => InternedGuardedSyntax.evaluate holds (language :: environment.map (meaning holds ambient)) body)
      have checked : ∀ argument current, Context current environment → Available current (.reference argument) → Heap current →
          Checked (callback body environment argument current) (fun value => ∀ holds ambient,
            argument ∉ InternedProfileCallbackForm.captures
              (InternedFreeNameForm.symbolic body (environment.map InternedRootProfile.profile) (environment.map Value.free)) →
            least (fun candidate => meaning holds (bind ambient argument candidate) value) = expected holds ambient) := by
        intro argument current currentContext argumentAvailable currentHeap
        have localContext := currentContext.local argument argumentAvailable
        have verified := build_verified body _ current localContext.normal.facts localContext.inputs
        unfold callback
        apply bind_checked _ _ _ _ (build_language body (.reference argument :: environment) current localContext currentHeap)
        intro value after returned afterHeap observed
        have afterContext : Context after (.reference argument :: environment) := by
          simpa only [returned, Outcome.state] using localContext.build body
        have capturesContext : Context after environment :=
          ⟨afterContext.normal, fun value member => afterContext.inputs value (List.mem_cons_of_mem _ member),
            afterContext.profiles, afterContext.freeNames⟩
        apply done_checked
        · exact preserve after _ afterHeap (InternedStoredMuOrigins.filter_noNewMu argument value after)
        · intro holds ambient fresh
          apply filter_source_least holds ambient body environment argument value after capturesContext (verified.result value after returned) fresh
          intro other
          have referenceMeaning : meaning holds other (Value.reference argument : Value Symbol Guard) = other argument := by rw [meaning]
          simpa only [List.map_cons, referenceMeaning] using observed holds other
      have depthVerified := callback_verified body environment .depth state context.normal.facts
        (context.local .depth (depth_available state)).inputs
      have wholeVerified := build_verified (.binder smart body) environment state context.normal.facts context.inputs
      rw [build]
      change Checked ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary) _
      apply bind_checked _ _ _ _ (checked .depth state context (depth_available state) heap)
      intro depth afterDepth depthDone depthHeap _
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
      have depthAvailable := depthVerified.result depth afterDepth depthDone
      have fresh := ordinary_fresh_captures body environment state context depth afterDepth depthDone
      have ordinaryVerified := callback_verified body environment (.uninterned (ordinaryLevel depth)) afterDepth
        depthContext.normal.facts (depthContext.local _ (ordinary_available afterDepth _)).inputs
      apply bind_checked _ _ _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available afterDepth _) depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap ordinaryObserved
      have finalContext : Context afterOrdinary environment := by
        simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth _)
      have finalDepth : Available afterOrdinary depth := by
        simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth depthAvailable
      have finalOrdinary := ordinaryVerified.result ordinary afterOrdinary ordinaryDone
      have ordinaryExpected : ∀ holds ambient, least (fun candidate => meaning holds
          (bind ambient (.uninterned (ordinaryLevel depth)) candidate) ordinary) = expected holds ambient :=
        fun holds ambient => ordinaryObserved holds ambient fresh
      have retained := request_heap smart body environment depth ordinary afterOrdinary finalContext ordinaryHeap expected ordinaryExpected
        (fun argument current ctx available currentHeap fresh =>
          ⟨(checked argument current ctx available currentHeap).heap,
            fun value after returned holds ambient => (checked argument current ctx available currentHeap).result value after returned holds ambient fresh⟩)
      have whole : build (.binder smart body) environment state =
          request smart depth ordinary (callback body environment) afterOrdinary := by
        rw [build]
        change ((callback body environment .depth state).bind _) = _
        rw [depthDone]
        change ((callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind _) = _
        rw [ordinaryDone]
        rfl
      refine ⟨retained, ?_⟩
      intro value after returned holds ambient
      have afterHeap : Heap after := by simpa only [returned, Outcome.state] using retained
      have afterFacts : InternedNestedFacts.Facts after := by
        simpa only [whole, returned, Outcome.state] using wholeVerified.facts
      rw [InternedGuardedSyntax.evaluate]
      exact (request_language holds ambient smart body environment depth ordinary afterOrdinary finalContext.normal.facts
        finalDepth finalOrdinary value after returned afterFacts afterHeap).trans (ordinaryExpected holds ambient)
termination_by sizeOf expression

/-- Ordered source child execution retains the exact ordered list of independent languages. -/
theorem buildMany_language [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) :
    Checked (buildMany expressions environment state) (fun values => ∀ holds ambient,
      values.map (meaning holds ambient) = expressions.map (InternedGuardedSyntax.evaluate holds (environment.map (meaning holds ambient)))) := by
  cases expressions with
  | nil =>
      rw [buildMany]
      exact done_checked _ _ _ heap (by intro holds ambient; rfl)
  | cons first rest =>
      rw [buildMany]
      apply bind_checked _ _ _ _ (build_language first environment state context heap)
      intro value after returned afterHeap observed
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.build first
      apply bind_checked _ _ _ _ (buildMany_language rest environment after afterContext afterHeap)
      intro values final completed finalHeap matched
      apply done_checked _ _ _ finalHeap
      intro holds ambient
      rw [List.map_cons, List.map_cons, observed holds ambient, matched holds ambient]
termination_by sizeOf expressions

/-- Actual source edge execution retains complete guards, child order, and every accepting alternative. -/
theorem buildEdges_language [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) :
    Checked (buildEdges expressions environment state) (fun values => ∀ holds ambient term,
      (∃ edge ∈ values, edgeMeaning holds ambient edge term) ↔
        ∃ edge ∈ expressions, InternedGuardedSyntax.edgeMeaning holds (environment.map (meaning holds ambient)) edge term) := by
  cases expressions with
  | nil =>
      rw [buildEdges]
      exact done_checked _ _ _ heap (by intro holds ambient term; simp only [List.not_mem_nil, false_and, exists_false])
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          have verified := buildMany_verified children environment state context.normal.facts context.inputs
          rw [buildEdges]
          apply bind_checked _ _ _ _ (buildMany_language children environment state context heap)
          intro values after returned afterHeap observed
          have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many children
          have available := verified.result values after returned
          let actual := run (makeEdge symbol guard values) after
          have edgeContext : Context actual.2 environment := afterContext.edge symbol guard values available
          have headSame := fun holds ambient => makeEdge_language holds ambient (environment.map (meaning holds ambient)) symbol guard values children
            after afterContext.normal.facts.coherent afterContext.normal.facts.cached available (observed holds ambient)
          simp only [work, Outcome.bind]
          change Checked ((buildEdges rest environment actual.2).bind _) _
          apply bind_checked _ _ _ _ (buildEdges_language rest environment actual.2 edgeContext afterHeap)
          intro edges final completed finalHeap matched
          apply done_checked _ _ _ finalHeap
          intro holds ambient term
          rw [exists_cons, exists_cons]
          exact or_congr (iff_of_eq (congrFun (headSame holds ambient) term)) (matched holds ambient term)
termination_by sizeOf expressions
end

/-- A completed closed source plan has exactly its independent guarded least language. -/
theorem closed_language [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (done : build expression [] empty = .done value state) (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) :
    meaning holds ambient value = InternedGuardedSyntax.evaluate holds [] expression :=
  (build_language expression [] empty empty_context empty_heap).result value state done holds ambient

/-- Complete and pending closed executions retain the independently derived semantic probe heap. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Heap (build expression [] empty).state :=
  (build_language expression [] empty empty_context empty_heap).heap

end MicroCFTA.InternedGuardedExecution
