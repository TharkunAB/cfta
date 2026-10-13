import MicroCFTA.InternedSpecialKeyReadiness
import MicroCFTA.InternedPendingScopes

/-!
# Full nested source execution cannot create a special pending encounter

Every actual depth-body completion prepares the two special keys at all
of its nested syntax sites. Later literal-reference aliases preserve
those classes. Coverage accounts for any pre-existing pending allowance.
-/
namespace MicroCFTA.InternedSpecialKeyCompletion
open Cache InternedConstructorTemplates InternedNestedConstruction InternedNestedSpecialization
open InternedRecordCoherence InternedProbeProvenance InternedNestedProvenance
open InternedStoredMuOrigins InternedNestedMissReadback InternedNestedCoverage
open InternedProfileTraceSites InternedSpecialProbeKeys InternedSpecialKeyReadiness
open InternedBinderProtocol (Reference NodeKey)

/-- A source outcome does not stop at either smart-empty canonical key. -/
def Safe (outcome : Outcome Symbol Guard Result) : Prop :=
  ∀ uses final, outcome ≠ .pending (key uses) final

/-- A completed value cannot be a pending encounter. -/
theorem safe_done (value : Result) (state : State Symbol Guard) : Safe (.done value state) := by
  intro uses final same
  cases same

/-- Sequential source execution preserves exclusion of the two special pending keys. -/
theorem bind_safe (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : Safe outcome)
    (later : ∀ value after, outcome = .done value after → Safe (next value after)) : Safe (outcome.bind next) := by
  cases outcome with
  | pending name state =>
      intro uses final stopped
      have same := Outcome.pending.inj stopped
      apply first uses final
      rw [same.1, same.2]
  | done value state => exact later value state rfl

/-- Ordinary constructors always return a complete record. -/
theorem work_safe [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (state : State Symbol Guard) : Safe (work computation state) := safe_done _ _

section
variable [DecidableEq (EdgeKey Symbol Guard)]
mutual
/-- Arbitrary full syntax excludes special pending encounters once its active source sites are prepared. -/
theorem build_safe (expression : Syntax Symbol Guard) (names : List Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (waiting : List NodeKey)
    (covered : Covered waiting state) (ready : Ready waiting expression names.length state) :
    Safe (build expression (names.map Value.reference) state) := by
  cases expression with
  | empty | var index => simpa only [build] using safe_done _ _
  | node edges =>
      rw [build]
      apply bind_safe _ _ (buildEdges_safe edges names state context waiting covered (by
        intro symbol constraint children edge child member
        exact ready.descendant (.node edge member (.here child))))
      intro values after completed
      exact work_safe _ _
  | union members =>
      rw [build]
      apply bind_safe _ _ (buildMany_safe members names state context waiting covered (by
        intro child member
        exact ready.descendant (.union member (.here child))))
      intro values after completed
      exact work_safe _ _
  | binder smart body =>
      have invoke : ∀ (name : Reference) current, Context current (names.map Value.reference) →
          Available current (.reference name) → ∀ active, Covered active current →
          Ready active body (names.length + 1) current → Safe (callback body (names.map Value.reference) name current) := by
        intro name current currentContext argument active currentCovered currentReady
        have localContext : Context current ((name :: names).map Value.reference) := by
          refine ⟨currentContext.normal, ?_, currentContext.heap⟩
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact argument
          · exact currentContext.inputs value member
        apply bind_safe _ _ (build_safe body (name :: names) current localContext active currentCovered currentReady)
        intro value after completed
        exact work_safe _ _
      have bodyReady : Ready waiting body (names.length + 1) state :=
        ready.descendant (.binder (.here body))
      rw [build]
      change Safe ((callback body (names.map Value.reference) .depth state).bind fun depth afterDepth =>
        (callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body (names.map Value.reference)) afterOrdinary)
      apply bind_safe _ _ (invoke .depth state context (depth_available state) waiting covered bodyReady)
      intro depth afterDepth depthDone
      have depthContext : Context afterDepth (names.map Value.reference) := by
        simpa only [depthDone, Outcome.state] using InternedSpecialKeyReadiness.Context.callback context body .depth (depth_available state)
      have depthVerified := callback_verified body (names.map Value.reference) .depth state context.normal.facts context.depth.inputs
      have depthGrowth : Grows state afterDepth := by simpa only [depthDone, Outcome.state] using depthVerified.growth
      have depthCovered := InternedPendingScopes.callback_covered body (names.map Value.reference) .depth state
        context.normal.facts.coherent.valid covered depth afterDepth depthDone
      apply bind_safe _ _ (invoke (.uninterned depth.depth) afterDepth depthContext (ordinary_available afterDepth depth.depth)
        waiting depthCovered (bodyReady.grows depthGrowth))
      intro ordinary afterOrdinary ordinaryDone
      have ordinaryContext : Context afterOrdinary (names.map Value.reference) := by
        simpa only [ordinaryDone, Outcome.state] using InternedSpecialKeyReadiness.Context.callback depthContext body (.uninterned depth.depth) (ordinary_available afterDepth depth.depth)
      have ordinaryInputs : Values afterDepth (.reference (.uninterned depth.depth) :: names.map Value.reference) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact ordinary_available afterDepth depth.depth
        · exact depthContext.inputs value member
      have ordinaryVerified := callback_verified body (names.map Value.reference) (.uninterned depth.depth) afterDepth depthContext.normal.facts ordinaryInputs
      have ordinaryGrowth : Grows afterDepth afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.growth
      have ordinaryCovered := InternedPendingScopes.callback_covered body (names.map Value.reference) (.uninterned depth.depth) afterDepth
        depthContext.normal.facts.coherent.valid depthCovered ordinary afterOrdinary ordinaryDone
      cases found : afterOrdinary.nodes.table (muKey depth ordinary) with
      | some entry =>
          cases stored : afterOrdinary.nodeRecords (muKey depth ordinary) with
          | some record => simpa only [request, found, stored] using safe_done (finish smart record) afterOrdinary
          | none =>
              intro uses final stopped
              simp only [request, found, stored, Outcome.pending.injEq] at stopped
              have sameKey := stopped.1
              have member : key uses ∈ waiting := by
                rcases ordinaryCovered.nodes _ entry found with member | ⟨record, complete⟩
                · simpa only [sameKey] using member
                · rw [stored] at complete; cases complete
              have classified := (source_classified body (names.map Value.reference) state afterDepth afterOrdinary context depth ordinary depthDone ordinaryDone uses).mp sameKey
              rw [reference_profiles] at classified
              obtain ⟨record, complete⟩ := (ready.grows (grows_trans depthGrowth ordinaryGrowth)) smart body 0 (.here _) names (by simp) uses member classified
              rw [← sameKey, stored] at complete
              cases complete
      | none =>
          let entry := Cache.intern afterOrdinary.nodes (muKey depth ordinary)
          let allocated := {afterOrdinary with nodes := entry.2}
          have growth : Grows afterOrdinary allocated :=
            ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
          have history := InternedFreshProbeKeys.intern_issued_extends afterOrdinary.nodes (muKey depth ordinary) ordinaryContext.normal.facts.coherent.valid.2
          have allocatedContext : Context allocated (names.map Value.reference) :=
            ⟨reserve_normal _ afterOrdinary ordinaryContext.normal,
              fun value member => (ordinaryContext.inputs value member).grows afterOrdinary allocated growth history,
              ordinaryContext.heap⟩
          have argument : Available allocated (.reference (.interned entry.1.identity)) :=
            (InternedConstructionProvenance.reserve_available _ afterOrdinary ordinaryContext.normal.facts.coherent ordinaryContext.normal.facts.cached).2
          obtain ⟨raw, afterRaw, rawDone, filterDone⟩ := bind_done _ _ _ _ depthDone
          have rawFacts := build_correct body (.reference .depth :: names.map Value.reference) state context.normal.facts.coherent.valid
          rw [rawDone] at rawFacts
          have filterGrowth := (work_correct (withoutSelfReference .depth raw) afterRaw rawFacts.1).2
          rw [filterDone] at filterGrowth
          have allGrowth : Grows afterRaw allocated := grows_trans filterGrowth (grows_trans ordinaryGrowth growth)
          have prepared : Ready (muKey depth ordinary :: waiting) body (names.length + 1) allocated := by
            exact ready_from_trace body (.depth :: names) state afterRaw allocated raw context.depth rawDone allGrowth _
          simp only [request, found]
          change Safe ((callback body (names.map Value.reference) (.interned entry.1.identity) allocated).bind _)
          apply bind_safe _ _ (invoke _ allocated allocatedContext argument _ (reserve_covered _ afterOrdinary ordinaryCovered) prepared)
          intro value after completed
          exact safe_done _ _
termination_by sizeOf expression

/-- Ordered source children retain the same prepared-site condition. -/
theorem buildMany_safe (expressions : List (Syntax Symbol Guard)) (names : List Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (waiting : List NodeKey)
    (covered : Covered waiting state)
    (ready : ∀ expression ∈ expressions, Ready waiting expression names.length state) :
    Safe (buildMany expressions (names.map Value.reference) state) := by
  cases expressions with
  | nil => simpa only [buildMany, buildEdges] using safe_done _ _
  | cons first rest =>
      rw [buildMany]
      apply bind_safe _ _ (build_safe first names state context waiting covered (ready first List.mem_cons_self))
      intro value after completed
      have afterContext : Context after (names.map Value.reference) := by
        simpa only [completed, Outcome.state] using context.build first
      have growth : Grows state after := by
        simpa only [completed, Outcome.state] using (build_correct first (names.map Value.reference) state context.normal.facts.coherent.valid).2
      have afterCovered := build_covered first _ state context.normal.facts.coherent.valid covered value after completed
      apply bind_safe _ _ (buildMany_safe rest names after afterContext waiting afterCovered
        (fun child member => (ready child (List.mem_cons_of_mem first member)).grows growth))
      intro values final completedRest
      exact safe_done _ _
termination_by sizeOf expressions

/-- Every actual edge child uses its source position before ordinary edge allocation. -/
theorem buildEdges_safe (expressions : List (EdgeSyntax Symbol Guard)) (names : List Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (waiting : List NodeKey)
    (covered : Covered waiting state)
    (ready : ∀ symbol constraint children, .mk symbol constraint children ∈ expressions →
      ∀ child ∈ children, Ready waiting child names.length state) :
    Safe (buildEdges expressions (names.map Value.reference) state) := by
  cases expressions with
  | nil => simpa only [buildMany, buildEdges] using safe_done _ _
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_safe _ _ (buildMany_safe children names state context waiting covered
            (ready symbol constraint children List.mem_cons_self))
          intro values after completed
          have afterContext : Context after (names.map Value.reference) := by
            simpa only [completed, Outcome.state] using context.many children
          have verified := buildMany_verified children (names.map Value.reference) state context.normal.facts context.inputs
          have growth : Grows state after := by simpa only [completed, Outcome.state] using verified.growth
          have valuesAvailable := verified.result values after completed
          have afterCovered := buildMany_covered children _ state context.normal.facts.coherent.valid covered values after completed
          apply bind_safe _ _ (work_safe _ _)
          intro edge afterEdge edgeDone
          have edgeContext : Context afterEdge (names.map Value.reference) := by
            have current := afterContext.edge symbol constraint values valuesAvailable
            change Context (work (makeEdge symbol constraint values) after).state _ at current
            simpa only [edgeDone, Outcome.state] using current
          have edgeGrowth : Grows after afterEdge := by
            simpa only [edgeDone, Outcome.state] using (work_correct (makeEdge symbol constraint values) after afterContext.normal.facts.coherent.valid).2
          have edgeCovered := work_covered (makeEdge symbol constraint values) after afterContext.normal.facts.coherent.valid afterCovered edge afterEdge edgeDone
          apply bind_safe _ _ (buildEdges_safe rest names afterEdge edgeContext waiting edgeCovered (by
            intro own guard ownChildren member child included
            exact (ready own guard ownChildren (List.mem_cons_of_mem _ member) child included).grows (grows_trans growth edgeGrowth)))
          intro edges final restDone
          exact safe_done _ _
termination_by sizeOf expressions
end
end

/-- No first execution of arbitrary closed syntax stops at either smart-empty canonical key. -/
theorem closed_safe [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Safe (build expression [] empty) := by
  apply build_safe expression [] empty ?_ [] InternedRecordCoherence.empty_correct.2 (ready_nil expression 0 empty)
  exact ⟨empty_normal, (by intro value member; cases member), InternedProfileHeap.empty_heap⟩

/-- The two-empty-probe key cannot be a pending result of a first closed source execution. -/
theorem closed_no_empty_key [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (final : State Symbol Guard) : build expression [] empty ≠ .pending (key false) final :=
  closed_safe expression false final

/-- The depth/self-sentinel key cannot be a pending result of a first closed source execution. -/
theorem closed_no_self_key [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (final : State Symbol Guard) : build expression [] empty ≠ .pending (key true) final :=
  closed_safe expression true final

end MicroCFTA.InternedSpecialKeyCompletion
