import MicroCFTA.InternedMarkedConstruction

/-!
# Complete first executions of the marked nested source fragment

Pending keys contain only active enclosing binders. Their preserved root
markers differ from the next binder's declared marker. Both source probes
therefore complete, and cache lookup cannot select an unfinished ancestor.
-/
namespace MicroCFTA.InternedMarkedConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedCoverage InternedNestedRootLabels
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
/-- Marker separation derived from the source expression excludes every pending ancestor on the first run. -/
theorem build_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (forbidden : List Symbol) (tagged : Tagged forbidden expression)
    (frames : List (Frame Symbol Guard)) (allowed : Allowed forbidden frames)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context frames environment state) :
    ∃ value final, build expression environment state = .done value final := by
  cases expression with
  | empty => exact ⟨.empty, state, by simp only [build]⟩
  | var index => exact ⟨environment[index]?.getD .empty, state, by simp only [build]⟩
  | node edges =>
      simp only [Tagged] at tagged
      obtain ⟨values, after, returned⟩ := buildEdges_completes edges forbidden tagged frames allowed environment state context
      simp only [build, returned, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | union members =>
      simp only [Tagged] at tagged
      obtain ⟨values, after, returned⟩ := buildMany_completes members forbidden tagged frames allowed environment state context
      simp only [build, returned, Outcome.bind, work]
      exact ⟨_, _, rfl⟩
  | binder smart body =>
      cases body <;> simp only [Tagged] at tagged
      case node edges =>
        obtain ⟨marker, fresh, marked, childrenTagged⟩ := tagged
        let callback := fun name current => (build (.node edges) (.reference name :: environment) current).bind
          fun value next => work (withoutSelfReference name value) next
        have invoke : ∀ currentFrames name current,
            Allowed (marker :: forbidden) currentFrames → Context currentFrames environment current →
            Available current (.reference name) →
            ∃ value final, callback name current = .done value final ∧ Root marker value ∧
              Context currentFrames environment final ∧ Available final value ∧ Grows current final := by
          intro currentFrames name current currentAllowed currentContext localAvailable
          have localContext := currentContext.local name localAvailable
          obtain ⟨value, final, completed⟩ := build_completes (.node edges) (marker :: forbidden)
            (by simpa only [Tagged] using childrenTagged) currentFrames currentAllowed (.reference name :: environment) current localContext
          have root := build_marked_root marker edges marked _ current localContext.facts localContext.inputs value final completed
          have verified := build_verified (.node edges) _ current localContext.facts localContext.inputs
          refine ⟨value, final, ?_, root, (localContext.afterBuild (.node edges) completed).dropLocal,
            verified.result value final completed, ?_⟩
          · simp only [callback, completed, Outcome.bind, work, root_filter marker value root]
          · simpa only [completed, Outcome.state] using verified.growth
        have outerAllowed : Allowed (marker :: forbidden) frames :=
          fun frame member => List.mem_cons_of_mem marker (allowed frame member)
        obtain ⟨depth, afterDepth, depthDone, depthRoot, depthContext, depthAvailable, depthGrowth⟩ :=
          invoke frames .depth state outerAllowed context (depth_available state)
        obtain ⟨ordinary, afterOrdinary, ordinaryDone, ordinaryRoot, ordinaryContext, ordinaryAvailable, ordinaryGrowth⟩ :=
          invoke frames (.uninterned depth.depth) afterDepth outerAllowed depthContext (ordinary_available afterDepth depth.depth)
        have depthResident : Resident afterOrdinary depth :=
          resident_grows afterDepth afterOrdinary ordinaryGrowth depth depthAvailable.resident
        have expanded : build (.binder smart (.node edges)) environment state =
            (callback .depth state).bind (fun depth afterDepth =>
              (callback (.uninterned depth.depth) afterDepth).bind (fun ordinary afterOrdinary =>
                request smart depth ordinary callback afterOrdinary)) := by rw [build]
        rw [expanded, depthDone]
        simp only [Outcome.bind]
        rw [ordinaryDone]
        cases found : afterOrdinary.nodes.table (muKey depth ordinary) with
        | some entry =>
            obtain ⟨record, stored⟩ := request_not_pending ordinaryContext allowed marker fresh depth ordinary depthRoot depthResident entry found
            simp only [request, found, stored]
            exact ⟨_, _, rfl⟩
        | none =>
            let frame : Frame Symbol Guard := ⟨marker, depth, ordinary, depthRoot⟩
            let entry := Cache.intern afterOrdinary.nodes frame.key
            let allocated := {afterOrdinary with nodes := entry.2}
            have newAllowed : Allowed (marker :: forbidden) (frame :: frames) := by
              intro selected member
              rcases List.mem_cons.mp member with rfl | member
              · exact List.mem_cons_self
              · exact outerAllowed selected member
            have allocatedContext := ordinaryContext.reserve frame depthResident
            have localAvailable : Available allocated (.reference (.interned entry.1.identity)) :=
              reference_available allocated _ (reserved_reference_issued afterOrdinary.nodes frame.key ordinaryContext.facts.coherent.valid.2)
            obtain ⟨bodyValue, afterBody, bodyDone, _⟩ := invoke (frame :: frames) (.interned entry.1.identity) allocated
              newAllowed allocatedContext localAvailable
            simp only [request, found]
            change ∃ value final, (callback (.interned entry.1.identity) allocated).bind _ = .done value final
            rw [bodyDone]
            exact ⟨_, _, rfl⟩
termination_by sizeOf expression

/-- Every finite ordered child list completes under the same syntax-derived pending-frame separation. -/
theorem buildMany_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (forbidden : List Symbol) (tagged : ManyTagged forbidden expressions)
    (frames : List (Frame Symbol Guard)) (allowed : Allowed forbidden frames)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context frames environment state) :
    ∃ values final, buildMany expressions environment state = .done values final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildMany]⟩
  | cons first rest =>
      simp only [ManyTagged] at tagged
      obtain ⟨value, after, headDone⟩ := build_completes first forbidden tagged.1 frames allowed environment state context
      obtain ⟨values, final, tailDone⟩ := buildMany_completes rest forbidden tagged.2 frames allowed environment after
        (context.afterBuild first headDone)
      exact ⟨value :: values, final, by simp only [buildMany, headDone, Outcome.bind, tailDone]⟩
termination_by sizeOf expressions

/-- Nested edge dependencies complete before source edge interning and later sibling evaluation. -/
theorem buildEdges_completes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (forbidden : List Symbol) (tagged : EdgesTagged forbidden expressions)
    (frames : List (Frame Symbol Guard)) (allowed : Allowed forbidden frames)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context frames environment state) :
    ∃ edges final, buildEdges expressions environment state = .done edges final := by
  cases expressions with
  | nil => exact ⟨[], state, by simp only [buildEdges]⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesTagged] at tagged
          obtain ⟨values, after, childrenDone⟩ := buildMany_completes children forbidden tagged.1 frames allowed environment state context
          have afterContext := context.afterMany children childrenDone
          have available := (buildMany_verified children environment state context.facts context.inputs).result values after childrenDone
          let edge := run (makeEdge symbol constraint values) after
          obtain ⟨edges, final, edgesDone⟩ := buildEdges_completes rest forbidden tagged.2 frames allowed environment edge.2
            (afterContext.afterEdge symbol constraint values available)
          refine ⟨edge.1 :: edges, final, ?_⟩
          simp only [buildEdges, childrenDone, Outcome.bind, work]
          change (buildEdges rest environment edge.2).bind _ = _
          rw [edgesDone]
          rfl
termination_by sizeOf expressions
end

/-- Every marked nested program starts from valid empty tables and completes on its first execution. -/
theorem closed_completes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (tagged : Tagged [] expression) : ∃ value final, build expression [] empty = .done value final := by
  apply build_completes expression [] tagged [] (by intro frame member; cases member) [] empty
  refine ⟨empty_facts, ?_, empty_correct.2, ?_⟩
  · intro value member; cases member
  · intro frame member; cases member

/-- A marked closed input cannot reach any pending canonical cache request. -/
theorem closed_not_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (tagged : Tagged [] expression) (key : InternedBinderProtocol.NodeKey) (state : State Symbol Guard) :
    build expression [] empty ≠ .pending key state := by
  obtain ⟨value, final, completed⟩ := closed_completes expression tagged
  simp [completed]

end MicroCFTA.InternedMarkedConstruction
