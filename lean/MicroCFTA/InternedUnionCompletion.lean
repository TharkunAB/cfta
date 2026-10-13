import MicroCFTA.InternedUnionConstruction

/-!
# First-run completion through root self filtering and union collapse

Source reference paths retain every active pending name in the inner depth
probe. Root self filtering removes only its own distinct sentinel. Each
pending frame therefore remains excluded after all union normalizations.
-/
namespace MicroCFTA.InternedUnionConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedCoverage InternedUnionReferences InternedLiveEdges InternedNormalizationFree
open InternedSelectivePreparedSites (NamesInterned)
open InternedRetainedConstruction (Frame Context Active request_not_pending)
open InternedBinderProtocol (Reference)

mutual
/-- Declared reference retention excludes pending readback through arbitrarily nested source construction. -/
theorem build_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (depth : Nat) (retentive : Retentive depth expression) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (names : NamesInterned frames) (state : State Symbol Guard)
    (context : Context frames environment state) (live : Live state) :
    ∃ value final, build expression environment state = .done value final := by
  cases expression with
  | empty => exact ⟨.empty, state, by simp only [build]⟩
  | var index => exact ⟨environment[index]?.getD .empty, state, by simp only [build]⟩
  | node edges =>
      simp only [Retentive] at retentive
      obtain ⟨values, after, returned⟩ := buildEdges_completes edges depth retentive frames environment length active names state context live
      simp only [build, returned, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | union members =>
      simp only [Retentive] at retentive
      obtain ⟨values, after, returned⟩ := buildMany_completes members depth retentive frames environment length active names state context live
      simp only [build, returned, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | binder smart body =>
      simp only [Retentive] at retentive
      obtain ⟨declared, bodyRetentive⟩ := retentive
      let callback := fun name current => (build body (.reference name :: environment) current).bind
          fun value next => work (withoutSelfReference name value) next
      have invoke : ∀ currentFrames name current,
          Active currentFrames (.reference name :: environment) → NamesInterned currentFrames →
          Context currentFrames environment current → Live current → Available current (.reference name) →
          ∃ value final, callback name current = .done value final ∧
            (∀ other, other ≠ name → .reference other ∈ environment → other ∈ value.free) ∧
            Context currentFrames environment final ∧ Available final value ∧ Grows current final ∧
            Extends current.nodes.issued final.nodes.issued ∧ Live final := by
        intro currentFrames name current currentActive currentNames currentContext currentLive localAvailable
        have localContext := currentContext.local name localAvailable
        obtain ⟨value, final, completed⟩ := build_completes body (depth + 1) bodyRetentive currentFrames
          (.reference name :: environment) (by simp [length]) currentActive currentNames current localContext currentLive
        have bodyContext := localContext.afterBuild body completed
        have verified := build_verified body _ current localContext.facts localContext.inputs
        have available := verified.result value final completed
        have bodyLive : Live final := by simpa only [completed, Outcome.state] using build_live body (.reference name :: environment) current currentLive
        let filtered := run (withoutSelfReference name value) final
        have filteredVerified := filter_verified name value final bodyContext.facts available
        have filteredContext : Context currentFrames environment filtered.2 :=
          bodyContext.dropLocal.advance filteredVerified rfl
            (run_covered _ final bodyContext.facts.coherent.valid bodyContext.covered)
        have bodyGrowth : Grows current final := by simpa only [completed, Outcome.state] using verified.growth
        have bodyHistory : Extends current.nodes.issued final.nodes.issued := by
          simpa only [completed, Outcome.state] using verified.history
        refine ⟨filtered.1, filtered.2, ?_, ?_, filteredContext, filteredVerified.result _ _ rfl,
          grows_trans bodyGrowth filteredVerified.growth, extends_trans bodyHistory filteredVerified.history,
          filter_live name value final bodyLive⟩
        · simp only [callback, completed, Outcome.bind, work, filtered]
        · intro other different present
          apply (filter_free_other name other value final bodyContext.facts.coherent bodyContext.facts.cached
            bodyContext.facts.linked bodyLive available different).mpr
          obtain ⟨index, bound, lookup⟩ := List.mem_iff_getElem.mp present
          apply build_retains (declared index (by simpa only [length] using bound)) _ current
            localContext.facts localContext.inputs currentLive other _ value final completed
          simp only [List.getElem?_cons_succ, List.getElem?_eq_getElem bound, lookup, Option.getD_some]
      have oldActive : ∀ name, Active frames (.reference name :: environment) :=
        fun _ frame member => List.mem_cons_of_mem _ (active frame member)
      obtain ⟨depthValue, afterDepth, depthDone, depthRefs, depthContext, depthAvailable, _, _, depthLive⟩ :=
        invoke frames .depth state (oldActive _) names context live (depth_available state)
      obtain ⟨ordinary, afterOrdinary, ordinaryDone, _, ordinaryContext, _, ordinaryGrowth, ordinaryHistory, ordinaryLive⟩ :=
        invoke frames (.uninterned depthValue.depth) afterDepth (oldActive _) names depthContext depthLive
          (ordinary_available afterDepth depthValue.depth)
      have depthResident : Resident afterOrdinary depthValue :=
        resident_grows afterDepth afterOrdinary ordinaryGrowth depthValue depthAvailable.resident
      have depthLater : Available afterOrdinary depthValue :=
        depthAvailable.grows afterDepth afterOrdinary ordinaryGrowth ordinaryHistory
      have expanded : build (.binder smart body) environment state =
          (callback .depth state).bind (fun depth afterDepth =>
            (callback (.uninterned depth.depth) afterDepth).bind (fun ordinary afterOrdinary =>
              request smart depth ordinary callback afterOrdinary)) := by rw [build]
      rw [expanded, depthDone]
      simp only [Outcome.bind]
      rw [ordinaryDone]
      cases found : afterOrdinary.nodes.table (muKey depthValue ordinary) with
      | some entry =>
          have retained : ∀ frame ∈ frames, frame.name ∈ depthValue.free := by
            intro frame member
            obtain ⟨identity, same⟩ := names frame member
            exact depthRefs frame.name (by simp [same]) (active frame member)
          obtain ⟨record, stored⟩ := request_not_pending ordinaryContext depthValue ordinary depthResident retained entry found
          simp only [request, found, stored]
          exact ⟨_, _, rfl⟩
      | none =>
          let entry := Cache.intern afterOrdinary.nodes (muKey depthValue ordinary)
          have absent : .interned entry.1.identity ∉ depthValue.free := by
            rw [intern_miss_identity afterOrdinary.nodes _ found]
            exact next_absent afterOrdinary.nodes ordinaryContext.facts.coherent.valid.2 depthValue depthLater.issued
          let frame : Frame Symbol Guard := ⟨.interned entry.1.identity, depthValue, ordinary, absent⟩
          let allocated := {afterOrdinary with nodes := entry.2}
          have allocatedContext : Context (frame :: frames) environment allocated := ordinaryContext.reserve frame depthResident
          have newActive : Active (frame :: frames) (.reference (.interned entry.1.identity) :: environment) := by
            intro selected member
            rcases List.mem_cons.mp member with rfl | member
            · exact List.mem_cons_self
            · exact oldActive _ selected member
          have newNames : NamesInterned (frame :: frames) := by
            intro selected member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨entry.1.identity, rfl⟩
            · exact names selected member
          have localAvailable : Available allocated (.reference (.interned entry.1.identity)) :=
            reference_available allocated _ (reserved_reference_issued afterOrdinary.nodes frame.key ordinaryContext.facts.coherent.valid.2)
          obtain ⟨bodyValue, afterBody, bodyDone, _⟩ := invoke (frame :: frames) (.interned entry.1.identity) allocated
            newActive newNames allocatedContext ordinaryLive localAvailable
          simp only [request, found]
          change ∃ value final, (callback (.interned entry.1.identity) allocated).bind _ = .done value final
          rw [bodyDone]
          exact ⟨_, _, rfl⟩
termination_by sizeOf expression

/-- Each child completes before its next sibling while retaining the same pending reference environment. -/
theorem buildMany_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (depth : Nat) (retentive : ManyRetentive depth expressions) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (names : NamesInterned frames) (state : State Symbol Guard)
    (context : Context frames environment state) (live : Live state) :
    ∃ values final, buildMany expressions environment state = .done values final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildMany]⟩
  | cons first rest =>
      simp only [ManyRetentive] at retentive
      obtain ⟨value, after, headDone⟩ := build_completes first depth retentive.1 frames environment length active names state context live
      obtain ⟨values, final, tailDone⟩ := buildMany_completes rest depth retentive.2 frames environment length active names after
        (context.afterBuild first headDone)
        (by simpa only [headDone, Outcome.state] using build_live first environment state live)
      exact ⟨value :: values, final, by simp only [buildMany, headDone, Outcome.bind, tailDone]⟩
termination_by sizeOf expressions

/-- Actual nested child computations and edge interning preserve the pending-frame separation. -/
theorem buildEdges_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (depth : Nat) (retentive : EdgesRetentive depth expressions) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (names : NamesInterned frames) (state : State Symbol Guard)
    (context : Context frames environment state) (live : Live state) :
    ∃ edges final, buildEdges expressions environment state = .done edges final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildEdges]⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesRetentive] at retentive
          obtain ⟨values, after, childrenDone⟩ := buildMany_completes children depth retentive.1 frames environment length active names state context live
          have afterContext := context.afterMany children childrenDone
          have available := (buildMany_verified children environment state context.facts context.inputs).result values after childrenDone
          let edge := run (makeEdge symbol constraint values) after
          obtain ⟨edges, final, edgesDone⟩ := buildEdges_completes rest depth retentive.2 frames environment length active names edge.2
            (afterContext.afterEdge symbol constraint values available)
            (makeEdge_live _ _ _ after (by simpa only [childrenDone, Outcome.state] using buildMany_live children environment state live))
          refine ⟨edge.1 :: edges, final, ?_⟩
          simp only [buildEdges, childrenDone, Outcome.bind, work]
          change (buildEdges rest environment edge.2).bind _ = _
          rw [edgesDone]
          rfl
termination_by sizeOf expressions
end

/-- Source-declared reference paths exclude pending readback from the actual empty-state execution. -/
theorem closed_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (retentive : Retentive 0 expression) : ∃ value final, build expression [] empty = .done value final := by
  apply build_completes expression 0 retentive [] [] rfl (by intro frame member; cases member)
    (by intro frame member; cases member) empty _ empty_live
  refine ⟨empty_facts, ?_, empty_correct.2, ?_⟩
  · intro value member; cases member
  · intro frame member; cases member

end MicroCFTA.InternedUnionConstruction
