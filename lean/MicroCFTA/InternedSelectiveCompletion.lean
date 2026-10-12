import MicroCFTA.InternedSelectiveConstruction

/-!
# Selective immediate-parent erasure and older-reference retention in one execution

An inner request can erase its immediate pending parent while retaining
older active ancestors. Exact earlier depth sites supply the erased-parent
replay. Direct source edges separate every other pending canonical key.
-/
namespace MicroCFTA.InternedSelectiveConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedCoverage InternedNestedRootReferences InternedNestedTraceSites InternedSelectivePreparedSites
open InternedRetainedConstruction (Frame Context Active request_not_pending)
open InternedBinderProtocol (Reference)

mutual
/-- Retention and normalized erased-call replay exclude pending readback in the same source execution. -/
theorem build_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (depth : Nat) (selective : Selective depth expression) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (names : NamesInterned frames) (state : State Symbol Guard) (context : Context frames environment state)
    (ready : HeadActive frames environment → Ready expression environment state) :
    ∃ value final, build expression environment state = .done value final := by
  classical
  cases expression with
  | empty => exact ⟨.empty, state, by simp only [build]⟩
  | var index => exact ⟨environment[index]?.getD .empty, state, by simp only [build]⟩
  | node edges =>
      simp only [Selective] at selective
      obtain ⟨values, after, returned⟩ := buildEdges_completes edges depth selective frames environment length active names state context
        (fun pending => ready_node (ready pending))
      simp only [build, returned, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | union members =>
      simp only [Selective] at selective
      obtain ⟨values, after, returned⟩ := buildMany_completes members depth selective frames environment length active names state context
        (fun pending => ready_union (ready pending))
      simp only [build, returned, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | binder smart body =>
      cases body <;> simp only [Selective] at selective
      case node edges =>
        obtain ⟨⟨keepHead, declared, erased⟩, childrenSelective⟩ := selective
        by_cases headSafe : keepHead = true ∨ ¬ HeadActive frames environment
        · let callback := fun name current => (build (.node edges) (.reference name :: environment) current).bind
            fun value next => work (withoutSelfReference name value) next
          have invoke : ∀ currentFrames name current,
              Active currentFrames (.reference name :: environment) → NamesInterned currentFrames → Context currentFrames environment current →
              (HeadActive currentFrames (.reference name :: environment) → Ready (.node edges) (.reference name :: environment) current) → Available current (.reference name) →
              ∃ value final, callback name current = .done value final ∧
                (∀ index other, index < depth → (keepHead = true ∨ 0 < index) → environment[index]?.getD .empty = .reference other → other ∈ value.free) ∧
                Context currentFrames environment final ∧ Available final value ∧ Grows current final ∧
                Extends current.nodes.issued final.nodes.issued ∧
                build (.node edges) (.reference name :: environment) current = .done value final := by
            intro currentFrames name current currentActive currentNames currentContext currentReady localAvailable
            have localContext := currentContext.local name localAvailable
            obtain ⟨value, final, completed⟩ := build_completes (.node edges) (depth + 1)
              (by simpa only [Selective] using childrenSelective) currentFrames (.reference name :: environment)
              (by simp [length]) currentActive currentNames current localContext currentReady
            have verified := build_verified (.node edges) _ current localContext.facts localContext.inputs
            refine ⟨value, final, ?_, ?_, (localContext.afterBuild (.node edges) completed).dropLocal,
              verified.result value final completed, ?_, ?_, completed⟩
            · simp only [callback, completed, Outcome.bind, work,
                build_node_filter edges _ current localContext.facts localContext.inputs value final completed name final]
            · intro index other bound allowed lookup
              obtain ⟨symbol, constraint, edge⟩ := declared index bound allowed
              apply build_node_reference edges _ current localContext.facts localContext.inputs value final completed
                symbol constraint (index + 1) other edge
              simpa only [List.getElem?_cons_succ] using lookup
            · simpa only [completed, Outcome.state] using verified.growth
            · simpa only [completed, Outcome.state] using verified.history
          have oldActive : ∀ name, Active frames (.reference name :: environment) :=
            fun _ frame member => List.mem_cons_of_mem _ (active frame member)
          obtain ⟨depthValue, afterDepth, depthDone, depthRefs, depthContext, depthAvailable, depthGrowth, _, depthBodyDone⟩ :=
            invoke frames .depth state (oldActive _) names context
              (fun impossible => False.elim (head_depth_inactive frames environment names impossible)) (depth_available state)
          obtain ⟨ordinary, afterOrdinary, ordinaryDone, _, ordinaryContext, _, ordinaryGrowth, ordinaryHistory, _⟩ :=
            invoke frames (.uninterned depthValue.depth) afterDepth (oldActive _) names depthContext
              (fun impossible => False.elim (head_ordinary_inactive frames environment names depthValue.depth impossible))
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
                (retained_frames frames environment depth length active keepHead headSafe depthValue depthRefs) entry found
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
              have newNames : NamesInterned (frame :: frames) := by
                intro selected member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨entry.1.identity, rfl⟩
                · exact names selected member
              obtain ⟨bodyValue, afterBody, bodyDone, _⟩ := invoke (frame :: frames) (.interned entry.1.identity) allocated
                newActive newNames allocatedContext (fun _ => ready_from_trace (.node edges) environment
                  (.reference (.interned entry.1.identity)) state depthValue afterDepth allocated
                  context.facts.coherent depthBodyDone
                  (grows_trans ordinaryGrowth ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩)) localAvailable
              simp only [request, found]
              change ∃ value final, (callback (.interned entry.1.identity) allocated).bind _ = .done value final
              rw [bodyDone]
              exact ⟨_, _, rfl⟩
        · have notKept : keepHead ≠ true := fun equal => headSafe (.inl equal)
          have falseMode : keepHead = false := by cases keepHead <;> simp_all
          have activeHead : HeadActive frames environment := by
            by_cases present : HeadActive frames environment
            · exact present
            · exact False.elim (headSafe (.inr present))
          exact (ready activeHead).complete (.binder 0 smart (.node edges) (erased falseMode)) context.facts.coherent
termination_by sizeOf expression

/-- Each child completes before its next sibling while retaining the same pending reference environment. -/
theorem buildMany_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (depth : Nat) (selective : ManySelective depth expressions) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (names : NamesInterned frames) (state : State Symbol Guard) (context : Context frames environment state)
    (ready : HeadActive frames environment → ManyReady expressions environment state) :
    ∃ values final, buildMany expressions environment state = .done values final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildMany]⟩
  | cons first rest =>
      simp only [ManySelective] at selective
      obtain ⟨value, after, headDone⟩ := build_completes first depth selective.1 frames environment length active names state context
        (fun pending => ready pending first List.mem_cons_self)
      have headGrowth := build_correct first environment state context.facts.coherent.valid
      rw [headDone] at headGrowth
      obtain ⟨values, final, tailDone⟩ := buildMany_completes rest depth selective.2 frames environment length active names after
        (context.afterBuild first headDone)
        (fun pending child member => ((ready pending) child (List.mem_cons_of_mem _ member)).grows headGrowth.2)
      exact ⟨value :: values, final, by simp only [buildMany, headDone, Outcome.bind, tailDone]⟩
termination_by sizeOf expressions

/-- Actual nested child computations and edge interning preserve the pending-frame separation. -/
theorem buildEdges_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (depth : Nat) (selective : EdgesSelective depth expressions) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (names : NamesInterned frames) (state : State Symbol Guard) (context : Context frames environment state)
    (ready : HeadActive frames environment → EdgesReady expressions environment state) :
    ∃ edges final, buildEdges expressions environment state = .done edges final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildEdges]⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesSelective] at selective
          obtain ⟨values, after, childrenDone⟩ := buildMany_completes children depth selective.1 frames environment length active names state context
            (fun pending => ready pending symbol constraint children List.mem_cons_self)
          have afterContext := context.afterMany children childrenDone
          have available := (buildMany_verified children environment state context.facts context.inputs).result values after childrenDone
          let edge := run (makeEdge symbol constraint values) after
          have childrenGrowth := buildMany_correct children environment state context.facts.coherent.valid
          rw [childrenDone] at childrenGrowth
          have edgeGrowth := InternedConstructorTemplates.run_correct (makeEdge symbol constraint values) after afterContext.facts.coherent.valid
          obtain ⟨edges, final, edgesDone⟩ := buildEdges_completes rest depth selective.2 frames environment length active names edge.2
            (afterContext.afterEdge symbol constraint values available)
            (fun pending own guard children member =>
              ((ready pending) own guard children (List.mem_cons_of_mem _ member)).grows
                (grows_trans childrenGrowth.2 edgeGrowth.2))
          refine ⟨edge.1 :: edges, final, ?_⟩
          simp only [buildEdges, childrenDone, Outcome.bind, work]
          change (buildEdges rest environment edge.2).bind _ = _
          rw [edgesDone]
          rfl
termination_by sizeOf expressions
end

/-- Source-declared selective retention and immediate-parent erasure complete directly from empty caches. -/
theorem closed_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (selective : Selective 0 expression) : ∃ value final, build expression [] empty = .done value final := by
  apply build_completes expression 0 selective [] [] rfl (by intro frame member; cases member) (by intro frame member; cases member) empty
  · refine ⟨empty_facts, ?_, empty_correct.2, ?_⟩
    · intro value member; cases member
    · intro frame member; cases member
  · rintro ⟨frame, impossible, _⟩
    cases impossible

end MicroCFTA.InternedSelectiveConstruction
