import MicroCFTA.InternedCombinedConstruction

/-!
# Combined completion through actual pending source contexts

Retained-reference binders can contain closed independent and erased-body
subprograms. First depth traces prepare their exact source sites before any
surrounding reservation. Fresh callbacks reuse those completed requests.
-/
namespace MicroCFTA.InternedCombinedConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedCoverage InternedNestedRootReferences InternedNestedTraceSites InternedNestedPreparedSites
open InternedRetainedConstruction (Frame Context Active request_not_pending)
open InternedBinderProtocol (Reference)

mutual
/-- Declared reference retention excludes pending readback through arbitrarily nested source construction. -/
theorem build_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (depth : Nat) (combined : Combined depth expression) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (state : State Symbol Guard) (context : Context frames environment state)
    (ready : frames ≠ [] → Ready expression state) :
    ∃ value final, build expression environment state = .done value final := by
  rw [Combined.eq_def] at combined
  rcases combined with leaf | combined
  · by_cases none : frames = []
    · subst frames
      exact leaf_completes expression leaf environment state context.facts.coherent context.covered
    · obtain ⟨value, completed⟩ := (ready none).complete leaf.1 environment
      exact ⟨value, state, completed⟩
  · cases expression with
    | empty => exact ⟨.empty, state, by simp only [build]⟩
    | var index => exact ⟨environment[index]?.getD .empty, state, by simp only [build]⟩
    | node edges =>
        obtain ⟨values, after, returned⟩ := buildEdges_completes edges depth combined frames environment length active state context
          (fun pending => ready_node (ready pending))
        simp only [build, returned, Outcome.bind, work]
        exact ⟨_, _, rfl⟩
    | union members =>
        obtain ⟨values, after, returned⟩ := buildMany_completes members depth combined frames environment length active state context
          (fun pending => ready_union (ready pending))
        simp only [build, returned, Outcome.bind, work]
        exact ⟨_, _, rfl⟩
    | binder smart body =>
        cases body <;> simp only at combined
        case node edges =>
          obtain ⟨declared, childrenCombined⟩ := combined
          let callback := fun name current => (build (.node edges) (.reference name :: environment) current).bind
            fun value next => work (withoutSelfReference name value) next
          have invoke : ∀ currentFrames name current,
              Active currentFrames (.reference name :: environment) → Context currentFrames environment current →
              (currentFrames ≠ [] → Ready (.node edges) current) → Available current (.reference name) →
              ∃ value final, callback name current = .done value final ∧
                (∀ other, .reference other ∈ environment → other ∈ value.free) ∧
                Context currentFrames environment final ∧ Available final value ∧ Grows current final ∧
                Extends current.nodes.issued final.nodes.issued ∧
                build (.node edges) (.reference name :: environment) current = .done value final := by
            intro currentFrames name current currentActive currentContext currentReady localAvailable
            have localContext := currentContext.local name localAvailable
            obtain ⟨value, final, completed⟩ := build_completes (.node edges) (depth + 1)
              (by rw [Combined]; exact Or.inr childrenCombined) currentFrames (.reference name :: environment)
              (by simp [length]) currentActive current localContext currentReady
            have verified := build_verified (.node edges) _ current localContext.facts localContext.inputs
            refine ⟨value, final, ?_, ?_, (localContext.afterBuild (.node edges) completed).dropLocal,
              verified.result value final completed, ?_, ?_, completed⟩
            · simp only [callback, completed, Outcome.bind, work,
                build_node_filter edges _ current localContext.facts localContext.inputs value final completed name final]
            · intro other present
              obtain ⟨index, bound, lookup⟩ := List.mem_iff_getElem.mp present
              obtain ⟨symbol, constraint, edge⟩ := declared index (by simpa only [length] using bound)
              apply build_node_reference edges _ current localContext.facts localContext.inputs value final completed
                symbol constraint (index + 1) other edge
              simp only [List.getElem?_cons_succ, List.getElem?_eq_getElem bound, lookup, Option.getD_some]
            · simpa only [completed, Outcome.state] using verified.growth
            · simpa only [completed, Outcome.state] using verified.history
          have oldActive : ∀ name, Active frames (.reference name :: environment) :=
            fun _ frame member => List.mem_cons_of_mem _ (active frame member)
          have bodyReady : frames ≠ [] → Ready (.node edges) state :=
            fun pending => (ready pending).descendant (.binder (.here (.node edges)))
          obtain ⟨depthValue, afterDepth, depthDone, depthRefs, depthContext, depthAvailable, depthGrowth, _, depthBodyDone⟩ :=
            invoke frames .depth state (oldActive _) context bodyReady (depth_available state)
          obtain ⟨ordinary, afterOrdinary, ordinaryDone, _, ordinaryContext, _, ordinaryGrowth, ordinaryHistory, _⟩ :=
            invoke frames (.uninterned depthValue.depth) afterDepth (oldActive _) depthContext
                (fun pending => (bodyReady pending).grows context.facts.coherent.valid depthGrowth)
              (ordinary_available afterDepth depthValue.depth)
          have depthResident : Resident afterOrdinary depthValue :=
            resident_grows afterDepth afterOrdinary ordinaryGrowth depthValue depthAvailable.resident
          have depthLater : Available afterOrdinary depthValue :=
            depthAvailable.grows afterDepth afterOrdinary ordinaryGrowth ordinaryHistory
          have expanded : build (.binder smart (.node edges)) environment state =
              (callback .depth state).bind (fun depth afterDepth =>
                (callback (.uninterned depth.depth) afterDepth).bind (fun ordinary afterOrdinary =>
                  request smart depth ordinary callback afterOrdinary)) := by rw [build]
          rw [expanded, depthDone]
          simp only [Outcome.bind]
          rw [ordinaryDone]
          cases found : afterOrdinary.nodes.table (muKey depthValue ordinary) with
          | some entry =>
              obtain ⟨record, stored⟩ := request_not_pending ordinaryContext depthValue ordinary depthResident
                (fun frame member => depthRefs frame.name (active frame member)) entry found
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
              have localAvailable : Available allocated (.reference (.interned entry.1.identity)) :=
                reference_available allocated _ (reserved_reference_issued afterOrdinary.nodes frame.key ordinaryContext.facts.coherent.valid.2)
              obtain ⟨bodyValue, afterBody, bodyDone, _⟩ := invoke (frame :: frames) (.interned entry.1.identity) allocated
                newActive allocatedContext (fun _ => ready_from_trace (.node edges)
                  (.reference .depth :: environment) state depthValue afterDepth allocated
                  context.facts.coherent.valid depthBodyDone
                  (grows_trans ordinaryGrowth ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩)) localAvailable
              simp only [request, found]
              change ∃ value final, (callback (.interned entry.1.identity) allocated).bind _ = .done value final
              rw [bodyDone]
              exact ⟨_, _, rfl⟩
termination_by sizeOf expression

/-- Each child completes before its next sibling while retaining the same pending reference environment. -/
theorem buildMany_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (depth : Nat) (combined : ManyCombined depth expressions) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (state : State Symbol Guard) (context : Context frames environment state)
    (ready : frames ≠ [] → ManyReady expressions state) :
    ∃ values final, buildMany expressions environment state = .done values final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildMany]⟩
  | cons first rest =>
      simp only [ManyCombined] at combined
      obtain ⟨value, after, headDone⟩ := build_completes first depth combined.1 frames environment length active state context
        (fun pending => ready pending first List.mem_cons_self)
      have headGrowth := build_correct first environment state context.facts.coherent.valid
      rw [headDone] at headGrowth
      obtain ⟨values, final, tailDone⟩ := buildMany_completes rest depth combined.2 frames environment length active after
        (context.afterBuild first headDone)
        (fun pending child member => ((ready pending) child (List.mem_cons_of_mem _ member)).grows context.facts.coherent.valid headGrowth.2)
      exact ⟨value :: values, final, by simp only [buildMany, headDone, Outcome.bind, tailDone]⟩
termination_by sizeOf expressions

/-- Actual nested child computations and edge interning preserve the pending-frame separation. -/
theorem buildEdges_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (depth : Nat) (combined : EdgesCombined depth expressions) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (state : State Symbol Guard) (context : Context frames environment state)
    (ready : frames ≠ [] → EdgesReady expressions state) :
    ∃ edges final, buildEdges expressions environment state = .done edges final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildEdges]⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesCombined] at combined
          obtain ⟨values, after, childrenDone⟩ := buildMany_completes children depth combined.1 frames environment length active state context
            (fun pending => ready pending symbol constraint children List.mem_cons_self)
          have afterContext := context.afterMany children childrenDone
          have available := (buildMany_verified children environment state context.facts context.inputs).result values after childrenDone
          let edge := run (makeEdge symbol constraint values) after
          have childrenGrowth := buildMany_correct children environment state context.facts.coherent.valid
          rw [childrenDone] at childrenGrowth
          have edgeGrowth := InternedConstructorTemplates.run_correct (makeEdge symbol constraint values) after afterContext.facts.coherent.valid
          obtain ⟨edges, final, edgesDone⟩ := buildEdges_completes rest depth combined.2 frames environment length active edge.2
            (afterContext.afterEdge symbol constraint values available)
            (fun pending own guard children member =>
              ((ready pending) own guard children (List.mem_cons_of_mem _ member)).grows
                context.facts.coherent.valid (grows_trans childrenGrowth.2 edgeGrowth.2))
          refine ⟨edge.1 :: edges, final, ?_⟩
          simp only [buildEdges, childrenDone, Outcome.bind, work]
          change (buildEdges rest environment edge.2).bind _ = _
          rw [edgesDone]
          rfl
termination_by sizeOf expressions
end

/-- A source program with declared enclosing-reference retention completes directly from empty caches. -/
theorem closed_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (combined : Combined 0 expression) : ∃ value final, build expression [] empty = .done value final := by
  apply build_completes expression 0 combined [] [] rfl (by intro frame member; cases member) empty
  · refine ⟨empty_facts, ?_, empty_correct.2, ?_⟩
    · intro value member; cases member
    · intro frame member; cases member
  · intro impossible
    exact False.elim (impossible rfl)

end MicroCFTA.InternedCombinedConstruction
