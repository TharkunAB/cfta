import MicroCFTA.InternedRetainedConstruction

/-!
# First-run completion with retained enclosing references

Each pending frame's fresh name is absent from its earlier depth probe.
Declared live unary edges put that name in every inner depth probe. Source
readback therefore cannot select any pending ancestor's canonical key.
-/
namespace MicroCFTA.InternedRetainedConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedCoverage InternedNestedRootReferences
open InternedBinderProtocol (Reference)

/-- A successful expression advances the original source context using only derived coverage and provenance. -/
theorem Context.afterBuild [DecidableEq (EdgeKey Symbol Guard)]
    {frames : List (Frame Symbol Guard)} {environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (context : Context frames environment state) (expression : Syntax Symbol Guard)
    (completed : build expression environment state = .done value final) : Context frames environment final :=
  context.advance (build_verified expression environment state context.facts context.inputs) completed
    (build_covered expression environment state context.facts.coherent.valid context.covered value final completed)

/-- Successful child lists retain the same exact active frame context. -/
theorem Context.afterMany [DecidableEq (EdgeKey Symbol Guard)]
    {frames : List (Frame Symbol Guard)} {environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (context : Context frames environment state) (expressions : List (Syntax Symbol Guard))
    (completed : buildMany expressions environment state = .done values final) : Context frames environment final :=
  context.advance (buildMany_verified expressions environment state context.facts context.inputs) completed
    (buildMany_covered expressions environment state context.facts.coherent.valid context.covered values final completed)

/-- Building one source edge preserves the existing pending frames and lexical input values. -/
theorem Context.afterEdge [DecidableEq (EdgeKey Symbol Guard)]
    {frames : List (Frame Symbol Guard)} {environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (context : Context frames environment state) (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (available : Values state values) :
    Context frames environment (run (makeEdge symbol constraint values) state).2 :=
  context.advance (edge_verified symbol constraint values state context.facts available) rfl
    (run_covered (makeEdge symbol constraint values) state context.facts.coherent.valid context.covered)

mutual
/-- Declared reference retention excludes pending readback through arbitrarily nested source construction. -/
theorem build_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (depth : Nat) (retentive : Retentive depth expression) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (state : State Symbol Guard) (context : Context frames environment state) :
    ∃ value final, build expression environment state = .done value final := by
  cases expression with
  | empty => exact ⟨.empty, state, by simp only [build]⟩
  | var index => exact ⟨environment[index]?.getD .empty, state, by simp only [build]⟩
  | node edges =>
      simp only [Retentive] at retentive
      obtain ⟨values, after, returned⟩ := buildEdges_completes edges depth retentive frames environment length active state context
      simp only [build, returned, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | union members =>
      simp only [Retentive] at retentive
      obtain ⟨values, after, returned⟩ := buildMany_completes members depth retentive frames environment length active state context
      simp only [build, returned, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | binder smart body =>
      cases body <;> simp only [Retentive] at retentive
      case node edges =>
        obtain ⟨declared, childrenRetentive⟩ := retentive
        let callback := fun name current => (build (.node edges) (.reference name :: environment) current).bind
          fun value next => work (withoutSelfReference name value) next
        have invoke : ∀ currentFrames name current,
            Active currentFrames (.reference name :: environment) → Context currentFrames environment current →
            Available current (.reference name) →
            ∃ value final, callback name current = .done value final ∧
              (∀ other, .reference other ∈ environment → other ∈ value.free) ∧
              Context currentFrames environment final ∧ Available final value ∧ Grows current final ∧
              Extends current.nodes.issued final.nodes.issued := by
          intro currentFrames name current currentActive currentContext localAvailable
          have localContext := currentContext.local name localAvailable
          obtain ⟨value, final, completed⟩ := build_completes (.node edges) (depth + 1)
            (by simpa only [Retentive] using childrenRetentive) currentFrames (.reference name :: environment)
            (by simp [length]) currentActive current localContext
          have verified := build_verified (.node edges) _ current localContext.facts localContext.inputs
          refine ⟨value, final, ?_, ?_, (localContext.afterBuild (.node edges) completed).dropLocal,
            verified.result value final completed, ?_, ?_⟩
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
        obtain ⟨depthValue, afterDepth, depthDone, depthRefs, depthContext, depthAvailable, _⟩ :=
          invoke frames .depth state (oldActive _) context (depth_available state)
        obtain ⟨ordinary, afterOrdinary, ordinaryDone, _, ordinaryContext, _, ordinaryGrowth, ordinaryHistory⟩ :=
          invoke frames (.uninterned depthValue.depth) afterDepth (oldActive _) depthContext
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
              newActive allocatedContext localAvailable
            simp only [request, found]
            change ∃ value final, (callback (.interned entry.1.identity) allocated).bind _ = .done value final
            rw [bodyDone]
            exact ⟨_, _, rfl⟩
termination_by sizeOf expression

/-- Each child completes before its next sibling while retaining the same pending reference environment. -/
theorem buildMany_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (depth : Nat) (retentive : ManyRetentive depth expressions) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (state : State Symbol Guard) (context : Context frames environment state) :
    ∃ values final, buildMany expressions environment state = .done values final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildMany]⟩
  | cons first rest =>
      simp only [ManyRetentive] at retentive
      obtain ⟨value, after, headDone⟩ := build_completes first depth retentive.1 frames environment length active state context
      obtain ⟨values, final, tailDone⟩ := buildMany_completes rest depth retentive.2 frames environment length active after
        (context.afterBuild first headDone)
      exact ⟨value :: values, final, by simp only [buildMany, headDone, Outcome.bind, tailDone]⟩
termination_by sizeOf expressions

/-- Actual nested child computations and edge interning preserve the pending-frame separation. -/
theorem buildEdges_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (depth : Nat) (retentive : EdgesRetentive depth expressions) (frames : List (Frame Symbol Guard))
    (environment : List (Value Symbol Guard)) (length : environment.length = depth)
    (active : Active frames environment) (state : State Symbol Guard) (context : Context frames environment state) :
    ∃ edges final, buildEdges expressions environment state = .done edges final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildEdges]⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesRetentive] at retentive
          obtain ⟨values, after, childrenDone⟩ := buildMany_completes children depth retentive.1 frames environment length active state context
          have afterContext := context.afterMany children childrenDone
          have available := (buildMany_verified children environment state context.facts context.inputs).result values after childrenDone
          let edge := run (makeEdge symbol constraint values) after
          obtain ⟨edges, final, edgesDone⟩ := buildEdges_completes rest depth retentive.2 frames environment length active edge.2
            (afterContext.afterEdge symbol constraint values available)
          refine ⟨edge.1 :: edges, final, ?_⟩
          simp only [buildEdges, childrenDone, Outcome.bind, work]
          change (buildEdges rest environment edge.2).bind _ = _
          rw [edgesDone]
          rfl
termination_by sizeOf expressions
end

/-- A source program with declared enclosing-reference retention completes directly from empty caches. -/
theorem closed_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (retentive : Retentive 0 expression) : ∃ value final, build expression [] empty = .done value final := by
  apply build_completes expression 0 retentive [] [] rfl (by intro frame member; cases member) empty
  refine ⟨empty_facts, ?_, empty_correct.2, ?_⟩
  · intro value member; cases member
  · intro frame member; cases member

end MicroCFTA.InternedRetainedConstruction
