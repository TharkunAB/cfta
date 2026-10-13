import MicroCFTA.InternedOrdinaryProducerCalls

/-!
# Producer callback equations retained by stopped source execution

The nested evaluator preserves each ordinary input's enclosing producer.
An active reservation retains the exact path into its original binder.
Each enclosing ordinary callback stops at the same exact request.
-/
namespace MicroCFTA.InternedPendingProducerCalls
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedSpecialization
open InternedFreeAbsenceContext InternedActiveSourceOrigins InternedRequestAgreement
open InternedNestedCoverage InternedPendingScopes InternedPendingLiveMismatch
open InternedLiveInputContext InternedOrdinaryProducerCalls
open InternedBinderProtocol (Reference NodeKey)

/-- Active source origins retain the introduction histories of their captured names. -/
def Scoped [DecidableEq (EdgeKey Symbol Guard)] (blocked : NodeKey) (stop : State Symbol Guard) (waiting : List NodeKey) (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) : Prop :=
  ∀ key ∈ waiting, ∃ origin : Origin Symbol Guard key, ∃ crossings,
    Inputs blocked stop (.binder origin.smart origin.body) origin.names origin.before ∧
    Path origin.body origin.localNames expression names crossings ∧ Grows origin.allocated state ∧
      ∀ crossing ∈ crossings, Grows origin.allocated crossing.before ∧ Grows crossing.start state

/-- Later source effects retain capture origins and descendant paths. -/
theorem Scoped.grows [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {before after : State Symbol Guard} (scope : Scoped blocked stop waiting expression names before)
    (growth : Grows before after) : Scoped blocked stop waiting expression names after := by
  intro key member
  obtain ⟨origin, crossings, inputs, path, initial, traces⟩ := scope key member
  exact ⟨origin, crossings, inputs, path, grows_trans initial growth,
    fun crossing included => ⟨(traces crossing included).1, grows_trans (traces crossing included).2 growth⟩⟩

/-- An ordinary child keeps the active capture origins. -/
theorem Scoped.node [DecidableEq (EdgeKey Symbol Guard)] {edges : List (EdgeSyntax Symbol Guard)}
    {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)} {child : Syntax Symbol Guard}
    {state : State Symbol Guard} (scope : Scoped blocked stop waiting (.node edges) names state)
    (edge : .mk symbol guard children ∈ edges) (member : child ∈ children) : Scoped blocked stop waiting child names state := by
  intro key included
  obtain ⟨origin, crossings, inputs, path, growth, traces⟩ := scope key included
  exact ⟨origin, crossings, inputs, by simpa using path.trans (.node edge member (.here child names)), growth, traces⟩

/-- A union operand keeps the active capture origins. -/
theorem Scoped.union [DecidableEq (EdgeKey Symbol Guard)] {members : List (Syntax Symbol Guard)}
    {child : Syntax Symbol Guard} {state : State Symbol Guard} (scope : Scoped blocked stop waiting (.union members) names state)
    (member : child ∈ members) : Scoped blocked stop waiting child names state := by
  intro key included
  obtain ⟨origin, crossings, inputs, path, growth, traces⟩ := scope key included
  exact ⟨origin, crossings, inputs, by simpa using path.trans (.union member (.here child names)), growth, traces⟩

/-- A nested lexical entry keeps all active capture origins. -/
theorem Scoped.enter [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard)
    (scope : Scoped blocked stop waiting (.binder crossing.smart crossing.body) crossing.names crossing.before) :
    Scoped blocked stop waiting crossing.body (crossing.name :: crossing.names) crossing.start := by
  intro key included
  obtain ⟨origin, crossings, inputs, path, growth, traces⟩ := scope key included
  refine ⟨origin, [crossing] ++ crossings, inputs, path.trans (.binder crossing (.here _ _)),
    grows_trans growth crossing.facts.2, ?_⟩
  intro selected member
  rcases List.mem_append.mp member with own | old
  · have same : selected = crossing := List.mem_singleton.mp own
    subst selected
    exact ⟨growth, grows_refl _⟩
  · exact ⟨(traces selected old).1, grows_trans (traces selected old).2 crossing.facts.2⟩

/-- A new reservation stores its original captured-name histories. -/
theorem Scoped.reserve [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (inputs : Inputs blocked stop (.binder origin.smart origin.body) origin.names origin.before)
    (older : Scoped blocked stop waiting origin.body origin.localNames origin.allocated) :
    Scoped blocked stop (key :: waiting) origin.body origin.localNames origin.allocated := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | previous
  · exact ⟨origin, [], inputs, .here _ _, grows_refl _, by intro crossing impossible; cases impossible⟩
  · exact older selected previous

/-- A stopped request retains the introductions of its active ancestor's ordinary captures. -/
def Encounter [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (final : State Symbol Guard) : Prop :=
  ∃ origin : Origin Symbol Guard key, ∃ smart body names before depth afterDepth ordinary crossings,
    Inputs key final (.binder origin.smart origin.body) origin.names origin.before ∧
    Context before names ∧ Path origin.body origin.localNames (.binder smart body) names crossings ∧
    Grows origin.allocated before ∧
    (∀ crossing ∈ crossings, Grows origin.allocated crossing.before ∧ Grows crossing.start before) ∧
    callback body (names.map Value.reference) .depth before = .done depth afterDepth ∧
    callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary final ∧
    Available final depth ∧ Available final ordinary ∧ key = muKey depth ordinary ∧ IsPending key final

mutual
/-- Every stopped source expression derives the exact source origin of its active reservation. -/
theorem build_encounter [DecidableEq (EdgeKey Symbol Guard)] (blocked : NodeKey) (stop : State Symbol Guard) (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state names) (inputs : Inputs blocked stop expression names state) (waiting : List NodeKey)
    (covered : Covered waiting state) (scope : Scoped blocked stop waiting expression names state)
    (pending : build expression (names.map Value.reference) state = .pending blocked stop) : Encounter blocked stop := by
  cases expression with
  | empty | var index => simp [build] at pending
  | node edges =>
      cases childrenDone : buildEdges edges (names.map Value.reference) state with
      | pending selected after =>
          simp only [build, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact buildEdges_encounter _ _ edges names state context (fun _ _ _ edge child member => inputs.node edge member) waiting covered
            (fun _ _ _ edge child member => scope.node edge member) childrenDone
      | done values after => simp [build, childrenDone, Outcome.bind, work] at pending
  | union members =>
      cases childrenDone : buildMany members (names.map Value.reference) state with
      | pending selected after =>
          simp only [build, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact buildMany_encounter _ _ members names state context (fun child member => inputs.union member) waiting covered
            (fun child member => scope.union member) childrenDone
      | done values after => simp [build, childrenDone, Outcome.bind, work] at pending
  | binder smart body =>
      have invoke : ∀ active name current, Context current (name :: names) → Inputs blocked stop body (name :: names) current →
          Covered active current → Scoped blocked stop active body (name :: names) current →
          callback body (names.map Value.reference) name current = .pending blocked stop → Encounter blocked stop := by
        intro active name current localContext localInputs currentCovered currentScope stopped
        cases returned : build body (.reference name :: names.map Value.reference) current with
        | pending inner finish =>
            simp only [callback, returned, Outcome.bind, Outcome.pending.injEq] at stopped
            obtain ⟨rfl, rfl⟩ := stopped
            exact build_encounter _ _ body (name :: names) current localContext localInputs active currentCovered currentScope
              (by simpa only [List.map_cons] using returned)
        | done value finish => simp [callback, returned, Outcome.bind, work] at stopped
      rw [build] at pending
      change ((callback body (names.map Value.reference) .depth state).bind fun depth afterDepth =>
        (callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body (names.map Value.reference)) afterOrdinary) = .pending blocked stop at pending
      have depthVerified := InternedPendingEncounter.callback_verified body _ .depth state context.normal.facts context.inputs (depth_available state)
      cases depthDone : callback body (names.map Value.reference) .depth state with
      | pending selected after =>
          simp only [depthDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          let crossing : Crossing Symbol Guard := ⟨smart, body, names, state, .depth, state, context, .depth⟩
          exact invoke waiting .depth state crossing.facts.1 (crossing_inputs crossing inputs depthDone) covered (scope.enter crossing) depthDone
      | done depth afterDepth =>
          have depthContext : Context afterDepth names := by
            simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
          have depthCovered := callback_covered body _ .depth state context.normal.facts.coherent.valid covered depth afterDepth depthDone
          have depthGrowth : Grows state afterDepth := by simpa only [depthDone, Outcome.state] using depthVerified.growth
          have ordinaryVerified := InternedPendingEncounter.callback_verified body _ (.uninterned depth.depth) afterDepth
            depthContext.normal.facts depthContext.inputs (ordinary_available afterDepth depth.depth)
          cases ordinaryDone : callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth with
          | pending selected after =>
              simp only [depthDone, Outcome.bind, ordinaryDone, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              let crossing : Crossing Symbol Guard :=
                ⟨smart, body, names, state, .uninterned depth.depth, afterDepth, context, .ordinary depth afterDepth depthDone⟩
              exact invoke waiting _ afterDepth crossing.facts.1 (crossing_inputs crossing inputs ordinaryDone) depthCovered (scope.enter crossing) ordinaryDone
          | done ordinary afterOrdinary =>
              have ordinaryContext : Context afterOrdinary names := by
                simpa only [ordinaryDone, Outcome.state] using
                  depthContext.callback body (.uninterned depth.depth) (ordinary_available afterDepth depth.depth)
              have ordinaryCovered := callback_covered body _ (.uninterned depth.depth) afterDepth
                depthContext.normal.facts.coherent.valid depthCovered ordinary afterOrdinary ordinaryDone
              have depthAvailable : Available afterOrdinary depth := by
                simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth (depthVerified.result _ _ depthDone)
              have ordinaryAvailable := ordinaryVerified.result ordinary afterOrdinary ordinaryDone
              simp only [depthDone, Outcome.bind, ordinaryDone] at pending
              cases found : afterOrdinary.nodes.table (muKey depth ordinary) with
              | some entry =>
                  cases stored : afterOrdinary.nodeRecords (muKey depth ordinary) with
                  | some value => simp [request, found, stored] at pending
                  | none =>
                      simp only [request, found, stored, Outcome.pending.injEq] at pending
                      obtain ⟨rfl, rfl⟩ := pending
                      have member : muKey depth ordinary ∈ waiting := by
                        rcases ordinaryCovered.nodes _ entry found with member | ⟨value, impossible⟩
                        · exact member
                        · rw [stored] at impossible; cases impossible
                      obtain ⟨origin, crossings, originInputs, path, growth, traces⟩ := scope _ member
                      exact ⟨origin, smart, body, names, state, depth, afterDepth, ordinary, crossings,
                        originInputs, context, path, growth, traces, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable,
                        rfl, ⟨entry, found⟩, stored⟩
              | none =>
                  let entry := Cache.intern afterOrdinary.nodes (muKey depth ordinary)
                  let allocated := {afterOrdinary with nodes := entry.2}
                  let crossing : Crossing Symbol Guard :=
                    ⟨smart, body, names, state, .interned entry.1.identity, allocated, context,
                      .fresh depth ordinary afterDepth afterOrdinary depthDone ordinaryDone found⟩
                  obtain ⟨rawDepth, afterRawDepth, rawDepthDone, _⟩ := bind_done _ _ _ _ depthDone
                  let origin : Origin Symbol Guard (muKey depth ordinary) :=
                    ⟨smart, body, names, state, rawDepth, afterRawDepth, depth, afterDepth, ordinary, afterOrdinary,
                      context, rawDepthDone, depthDone, ordinaryDone, rfl, found, ordinaryContext, depthAvailable, ordinaryAvailable⟩
                  have allocatedScope : Scoped blocked stop (muKey depth ordinary :: waiting) body
                      (.interned entry.1.identity :: names) allocated :=
                    Scoped.reserve origin inputs (scope.enter crossing)
                  have allocatedCovered := reserve_covered (muKey depth ordinary) afterOrdinary ordinaryCovered
                  simp only [request, found] at pending
                  change (callback body (names.map Value.reference) (.interned entry.1.identity) allocated).bind _ = .pending blocked stop at pending
                  cases bodyDone : callback body (names.map Value.reference) (.interned entry.1.identity) allocated with
                  | done value after => simp [bodyDone, Outcome.bind] at pending
                  | pending selected after =>
                      simp only [bodyDone, Outcome.bind, Outcome.pending.injEq] at pending
                      obtain ⟨rfl, rfl⟩ := pending
                      exact invoke (muKey depth ordinary :: waiting) _ allocated crossing.facts.1 (crossing_inputs crossing inputs bodyDone) allocatedCovered allocatedScope bodyDone
termination_by sizeOf expression

/-- The stopped member of an ordered child list retains the source paths of all active ancestors. -/
theorem buildMany_encounter [DecidableEq (EdgeKey Symbol Guard)] (blocked : NodeKey) (stop : State Symbol Guard) (expressions : List (Syntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state names) (inputs : ∀ expression ∈ expressions, Inputs blocked stop expression names state) (waiting : List NodeKey)
    (covered : Covered waiting state) (scope : ∀ expression ∈ expressions, Scoped blocked stop waiting expression names state)
    (pending : buildMany expressions (names.map Value.reference) state = .pending blocked stop) : Encounter blocked stop := by
  cases expressions with
  | nil => simp [buildMany] at pending
  | cons first rest =>
      have firstVerified := build_verified first _ state context.normal.facts context.inputs
      cases firstDone : build first (names.map Value.reference) state with
      | pending selected after =>
          simp only [buildMany, firstDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact build_encounter _ _ first names state context (inputs first List.mem_cons_self) waiting covered (scope first List.mem_cons_self) firstDone
      | done value after =>
          have afterContext : Context after names := by simpa only [firstDone, Outcome.state] using context.build first
          have afterCovered := build_covered first _ state context.normal.facts.coherent.valid covered value after firstDone
          have afterGrowth : Grows state after := by simpa only [firstDone, Outcome.state] using firstVerified.growth
          cases restDone : buildMany rest (names.map Value.reference) after with
          | done values last => simp [buildMany, firstDone, Outcome.bind, restDone] at pending
          | pending selected last =>
              simp only [buildMany, firstDone, Outcome.bind, restDone, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              exact buildMany_encounter _ _ rest names after afterContext
                (fun expression member => (inputs expression (List.mem_cons_of_mem first member)).grows afterGrowth) waiting afterCovered
                (fun expression member => (scope expression (List.mem_cons_of_mem first member)).grows afterGrowth) restDone
termination_by sizeOf expressions

/-- The stopped edge child retains actual source origins across all preceding child and edge effects. -/
theorem buildEdges_encounter [DecidableEq (EdgeKey Symbol Guard)] (blocked : NodeKey) (stop : State Symbol Guard) (expressions : List (EdgeSyntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state names) (inputs : ∀ symbol guard children, .mk symbol guard children ∈ expressions →
      ∀ expression ∈ children, Inputs blocked stop expression names state) (waiting : List NodeKey)
    (covered : Covered waiting state)
    (scope : ∀ symbol guard children, .mk symbol guard children ∈ expressions →
      ∀ expression ∈ children, Scoped blocked stop waiting expression names state)
    (pending : buildEdges expressions (names.map Value.reference) state = .pending blocked stop) : Encounter blocked stop := by
  cases expressions with
  | nil => simp [buildEdges] at pending
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have childVerified := buildMany_verified children _ state context.normal.facts context.inputs
          cases childrenDone : buildMany children (names.map Value.reference) state with
          | pending selected after =>
              simp only [buildEdges, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              exact buildMany_encounter _ _ children names state context (inputs symbol constraint children List.mem_cons_self) waiting covered
                (scope symbol constraint children List.mem_cons_self) childrenDone
          | done values after =>
              have afterContext : Context after names := by simpa only [childrenDone, Outcome.state] using context.many children
              have afterCovered := buildMany_covered children _ state context.normal.facts.coherent.valid covered values after childrenDone
              have afterGrowth : Grows state after := by simpa only [childrenDone, Outcome.state] using childVerified.growth
              let edge := run (makeEdge symbol constraint values) after
              have edgeVerified := edge_verified symbol constraint values after afterContext.normal.facts (childVerified.result _ _ childrenDone)
              have edgeContext : Context edge.2 names := afterContext.edge symbol constraint values (childVerified.result _ _ childrenDone)
              have edgeCovered := run_covered (makeEdge symbol constraint values) after afterContext.normal.facts.coherent.valid afterCovered
              cases restDone : buildEdges rest (names.map Value.reference) edge.2 with
              | done values last =>
                  simp only [buildEdges, childrenDone, Outcome.bind, work] at pending
                  change (buildEdges rest (names.map Value.reference) edge.2).bind _ = .pending blocked stop at pending
                  simp [restDone, Outcome.bind] at pending
              | pending selected last =>
                  simp only [buildEdges, childrenDone, Outcome.bind, work] at pending
                  change (buildEdges rest (names.map Value.reference) edge.2).bind _ = .pending blocked stop at pending
                  simp only [restDone, Outcome.bind, Outcome.pending.injEq] at pending
                  obtain ⟨rfl, rfl⟩ := pending
                  exact buildEdges_encounter _ _ rest names edge.2 edgeContext
                    (fun s g c member expression included =>
                      (inputs s g c (List.mem_cons_of_mem _ member) expression included).grows (grows_trans afterGrowth edgeVerified.growth)) waiting edgeCovered
                    (fun s g c member expression included =>
                      (scope s g c (List.mem_cons_of_mem _ member) expression included).grows (grows_trans afterGrowth edgeVerified.growth)) restDone
termination_by sizeOf expressions
end

/-- Closed source execution derives the completed ancestor probes and actual path of every hypothetical pending readback. -/
theorem closed_encounter [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    Encounter key final := by
  apply build_encounter key final expression [] empty
    ⟨empty_normal, (by intro value member; cases member), InternedProfileHeap.empty_heap, InternedFreeNameHeap.empty_heap⟩
    (by intro index level member; simp at member) [] empty_correct.2 (by intro key member; cases member) pending

end MicroCFTA.InternedPendingProducerCalls
