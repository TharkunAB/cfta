import MicroCFTA.InternedActiveSourceOrigins
import MicroCFTA.InternedPendingEncounter

/-!
# Actual active source origins at pending readback

The source induction retains the active ancestor's completed raw Depth
body and both normalized probes. It follows actual callback entries to
the stopped source binder. Closed execution derives every history field.
-/
namespace MicroCFTA.InternedPendingSourceOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedSpecialization
open InternedFreeAbsenceContext InternedActiveSourceOrigins InternedRequestAgreement
open InternedNestedCoverage InternedPendingScopes
open InternedBinderProtocol (Reference NodeKey)

/-- A pending source lookup retains its actual active ancestor and full descendant route. -/
def Encounter [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (final : State Symbol Guard) : Prop :=
  ∃ origin : Origin Symbol Guard key, ∃ smart body names before depth afterDepth ordinary crossings,
    Context before names ∧ Path origin.body origin.localNames (.binder smart body) names crossings ∧
    Grows origin.allocated before ∧
    (∀ crossing ∈ crossings, Grows origin.allocated crossing.before ∧ Grows crossing.start before) ∧
    callback body (names.map Value.reference) .depth before = .done depth afterDepth ∧
    callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary final ∧
    Available final depth ∧ Available final ordinary ∧ key = muKey depth ordinary ∧ IsPending key final

mutual
/-- Every stopped source expression derives the exact source origin of its active reservation. -/
theorem build_encounter [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state names) (waiting : List NodeKey)
    (covered : Covered waiting state) (scope : Scoped waiting expression names state)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : build expression (names.map Value.reference) state = .pending key final) : Encounter key final := by
  cases expression with
  | empty | var index => simp [build] at pending
  | node edges =>
      cases childrenDone : buildEdges edges (names.map Value.reference) state with
      | pending selected after =>
          simp only [build, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact buildEdges_encounter edges names state context waiting covered
            (fun _ _ _ edge child member => scope.node edge member) _ _ childrenDone
      | done values after => simp [build, childrenDone, Outcome.bind, work] at pending
  | union members =>
      cases childrenDone : buildMany members (names.map Value.reference) state with
      | pending selected after =>
          simp only [build, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact buildMany_encounter members names state context waiting covered
            (fun child member => scope.union member) _ _ childrenDone
      | done values after => simp [build, childrenDone, Outcome.bind, work] at pending
  | binder smart body =>
      have invoke : ∀ active name current, Context current (name :: names) →
          Covered active current → Scoped active body (name :: names) current → ∀ selected after,
          callback body (names.map Value.reference) name current = .pending selected after → Encounter selected after := by
        intro active name current localContext currentCovered currentScope selected after stopped
        cases returned : build body (.reference name :: names.map Value.reference) current with
        | pending inner finish =>
            simp only [callback, returned, Outcome.bind, Outcome.pending.injEq] at stopped
            obtain ⟨rfl, rfl⟩ := stopped
            exact build_encounter body (name :: names) current localContext active currentCovered currentScope _ _
              (by simpa only [List.map_cons] using returned)
        | done value finish => simp [callback, returned, Outcome.bind, work] at stopped
      rw [build] at pending
      change ((callback body (names.map Value.reference) .depth state).bind fun depth afterDepth =>
        (callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body (names.map Value.reference)) afterOrdinary) = .pending key final at pending
      have depthVerified := InternedPendingEncounter.callback_verified body _ .depth state context.normal.facts context.inputs (depth_available state)
      cases depthDone : callback body (names.map Value.reference) .depth state with
      | pending selected after =>
          simp only [depthDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          let crossing : Crossing Symbol Guard := ⟨smart, body, names, state, .depth, state, context, .depth⟩
          exact invoke waiting .depth state crossing.facts.1 covered (scope.enter crossing) _ _ depthDone
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
              exact invoke waiting _ afterDepth crossing.facts.1 depthCovered (scope.enter crossing) _ _ ordinaryDone
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
                      obtain ⟨origin, crossings, path, growth, traces⟩ := scope _ member
                      exact ⟨origin, smart, body, names, state, depth, afterDepth, ordinary, crossings,
                        context, path, growth, traces, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable,
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
                  have allocatedScope : Scoped (muKey depth ordinary :: waiting) body
                      (.interned entry.1.identity :: names) allocated :=
                    Scoped.reserve origin (scope.enter crossing)
                  have allocatedCovered := reserve_covered (muKey depth ordinary) afterOrdinary ordinaryCovered
                  simp only [request, found] at pending
                  change (callback body (names.map Value.reference) (.interned entry.1.identity) allocated).bind _ = .pending key final at pending
                  cases bodyDone : callback body (names.map Value.reference) (.interned entry.1.identity) allocated with
                  | done value after => simp [bodyDone, Outcome.bind] at pending
                  | pending selected after =>
                      simp only [bodyDone, Outcome.bind, Outcome.pending.injEq] at pending
                      obtain ⟨rfl, rfl⟩ := pending
                      exact invoke (muKey depth ordinary :: waiting) _ allocated crossing.facts.1 allocatedCovered allocatedScope _ _ bodyDone
termination_by sizeOf expression

/-- The stopped member of an ordered child list retains the source paths of all active ancestors. -/
theorem buildMany_encounter [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state names) (waiting : List NodeKey)
    (covered : Covered waiting state) (scope : ∀ expression ∈ expressions, Scoped waiting expression names state)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : buildMany expressions (names.map Value.reference) state = .pending key final) : Encounter key final := by
  cases expressions with
  | nil => simp [buildMany] at pending
  | cons first rest =>
      have firstVerified := build_verified first _ state context.normal.facts context.inputs
      cases firstDone : build first (names.map Value.reference) state with
      | pending selected after =>
          simp only [buildMany, firstDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact build_encounter first names state context waiting covered (scope first List.mem_cons_self) _ _ firstDone
      | done value after =>
          have afterContext : Context after names := by simpa only [firstDone, Outcome.state] using context.build first
          have afterCovered := build_covered first _ state context.normal.facts.coherent.valid covered value after firstDone
          have afterGrowth : Grows state after := by simpa only [firstDone, Outcome.state] using firstVerified.growth
          cases restDone : buildMany rest (names.map Value.reference) after with
          | done values last => simp [buildMany, firstDone, Outcome.bind, restDone] at pending
          | pending selected last =>
              simp only [buildMany, firstDone, Outcome.bind, restDone, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              exact buildMany_encounter rest names after afterContext waiting afterCovered
                (fun expression member => (scope expression (List.mem_cons_of_mem first member)).grows afterGrowth) _ _ restDone
termination_by sizeOf expressions

/-- The stopped edge child retains actual source origins across all preceding child and edge effects. -/
theorem buildEdges_encounter [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state names) (waiting : List NodeKey)
    (covered : Covered waiting state)
    (scope : ∀ symbol guard children, .mk symbol guard children ∈ expressions →
      ∀ expression ∈ children, Scoped waiting expression names state)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : buildEdges expressions (names.map Value.reference) state = .pending key final) : Encounter key final := by
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
              exact buildMany_encounter children names state context waiting covered
                (scope symbol constraint children List.mem_cons_self) _ _ childrenDone
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
                  change (buildEdges rest (names.map Value.reference) edge.2).bind _ = .pending key final at pending
                  simp [restDone, Outcome.bind] at pending
              | pending selected last =>
                  simp only [buildEdges, childrenDone, Outcome.bind, work] at pending
                  change (buildEdges rest (names.map Value.reference) edge.2).bind _ = .pending key final at pending
                  simp only [restDone, Outcome.bind, Outcome.pending.injEq] at pending
                  obtain ⟨rfl, rfl⟩ := pending
                  exact buildEdges_encounter rest names edge.2 edgeContext waiting edgeCovered
                    (fun s g c member expression included =>
                      (scope s g c (List.mem_cons_of_mem _ member) expression included).grows (grows_trans afterGrowth edgeVerified.growth)) _ _ restDone
termination_by sizeOf expressions
end

/-- Closed source execution derives the completed ancestor probes and actual path of every hypothetical pending readback. -/
theorem closed_encounter [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (pending : build expression [] empty = .pending key final) :
    Encounter key final := by
  apply build_encounter expression [] empty
    ⟨empty_normal, (by intro value member; cases member), InternedProfileHeap.empty_heap, InternedFreeNameHeap.empty_heap⟩
    [] empty_correct.2 (by intro key member; cases member) key final pending

end MicroCFTA.InternedPendingSourceOrigins
