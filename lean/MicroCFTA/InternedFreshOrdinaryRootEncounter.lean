import MicroCFTA.InternedFreshOrdinaryRootScope
import MicroCFTA.InternedFreshOrdinaryActiveEncounter

/-!
# Rooted actual source origins of repaired pending execution

The source induction retains the original path to every active reservation.
It also retains the existing descendant path, actual probe executions,
canonical pending key, and complete original semantic contexts.
-/
namespace MicroCFTA.InternedFreshOrdinaryRootEncounter
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request IsPending)
open InternedNestedFacts InternedNestedProvenance InternedNestedMissReadback
open InternedNestedSpecialization
open InternedFreshOrdinaryContext
open InternedFreshOrdinaryActiveOrigins (Origin Path Crossing callback_growing)
open InternedFreshOrdinarySourceHistory InternedFreshOrdinaryRootScope
open InternedNestedCoverage (reserve_covered run_covered)
open InternedBinderProtocol (Reference NodeKey)

/-- The exact pending encounter retains its active origin's path from the initial source call. -/
def Encounter [DecidableEq (EdgeKey Symbol Guard)] (root : Syntax Symbol Guard)
    (initial : List (Value Symbol Guard)) (key : NodeKey) (final : State Symbol Guard) : Prop :=
  ∃ origin : Origin Symbol Guard key, Rooted root initial origin ∧
    InternedFreshOrdinaryActiveEncounter.AtOrigin origin final

mutual
/-- Every stopped source expression derives the exact source origin of its active reservation. -/
theorem build_encounter [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard)) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment) (waiting : List NodeKey)
    (covered : Covered waiting state) (scope : Scoped root initial waiting expression environment state)
    (reached : Reached root initial expression environment state)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.build expression environment state = .pending key final) : Encounter root initial key final := by
  cases expression with
  | empty | var index => simp [InternedFreshOrdinaryConstruction.build] at pending
  | node edges =>
      cases childrenDone : InternedFreshOrdinaryConstruction.buildEdges edges environment state with
      | pending selected after =>
          simp only [InternedFreshOrdinaryConstruction.build, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact buildEdges_encounter root initial edges environment state context waiting covered
            (fun _ _ _ edge child member => scope.node edge member)
            (fun _ _ _ edge child member => reached.node edge member) _ _ childrenDone
      | done values after => simp [InternedFreshOrdinaryConstruction.build, childrenDone, Outcome.bind, work] at pending
  | union members =>
      cases childrenDone : InternedFreshOrdinaryConstruction.buildMany members environment state with
      | pending selected after =>
          simp only [InternedFreshOrdinaryConstruction.build, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact buildMany_encounter root initial members environment state context waiting covered
            (fun child member => scope.union member) (fun child member => reached.union member) _ _ childrenDone
      | done values after => simp [InternedFreshOrdinaryConstruction.build, childrenDone, Outcome.bind, work] at pending
  | binder smart body =>
      have invoke : ∀ active name current, Context current (.reference name :: environment) →
          Covered active current → Scoped root initial active body (.reference name :: environment) current →
          Reached root initial body (.reference name :: environment) current → ∀ selected after,
          InternedFreshOrdinaryFacts.callback body environment name current = .pending selected after → Encounter root initial selected after := by
        intro active name current localContext currentCovered currentScope currentReached selected after stopped
        cases returned : InternedFreshOrdinaryConstruction.build body (.reference name :: environment) current with
        | pending inner finish =>
            simp only [InternedFreshOrdinaryFacts.callback, returned, Outcome.bind, Outcome.pending.injEq] at stopped
            obtain ⟨rfl, rfl⟩ := stopped
            exact build_encounter root initial body (.reference name :: environment) current localContext active currentCovered currentScope currentReached _ _
              returned
        | done value finish => simp [InternedFreshOrdinaryFacts.callback, returned, Outcome.bind, work] at stopped
      rw [InternedFreshOrdinaryConstruction.build] at pending
      change ((InternedFreshOrdinaryFacts.callback body environment .depth state).bind fun depth afterDepth =>
        (InternedFreshOrdinaryFacts.callback body environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (InternedFreshOrdinaryFacts.callback body environment) afterOrdinary) = .pending key final at pending
      have depthVerified := InternedFreshOrdinaryEncounter.callback_verified body _ .depth state context.normal.facts context.inputs (depth_available state)
      cases depthDone : InternedFreshOrdinaryFacts.callback body environment .depth state with
      | pending selected after =>
          simp only [depthDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          let crossing : Crossing Symbol Guard := ⟨smart, body, environment, state, .depth, state, context, .depth⟩
          exact invoke waiting .depth state crossing.facts.1 covered (scope.enter crossing) (Reached.enter crossing reached) _ _ depthDone
      | done depth afterDepth =>
          have depthContext : Context afterDepth environment := by
            simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
          have depthCovered := InternedFreshOrdinaryCoverage.callback_covered body _ .depth state context.normal.facts.coherent.valid covered depth afterDepth depthDone
          have depthGrowth : Grows state afterDepth := by simpa only [depthDone, Outcome.state] using depthVerified.growth
          have ordinaryVerified := InternedFreshOrdinaryEncounter.callback_verified body _ (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth
            depthContext.normal.facts depthContext.inputs (ordinary_available afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
          cases ordinaryDone : InternedFreshOrdinaryFacts.callback body environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth with
          | pending selected after =>
              simp only [depthDone, Outcome.bind, ordinaryDone, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              let crossing : Crossing Symbol Guard :=
                ⟨smart, body, environment, state, .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth), afterDepth, context, .ordinary depth afterDepth depthDone⟩
              exact invoke waiting _ afterDepth crossing.facts.1 depthCovered (scope.enter crossing) (Reached.enter crossing reached) _ _ ordinaryDone
          | done ordinary afterOrdinary =>
              have ordinaryContext : Context afterOrdinary environment := by
                simpa only [ordinaryDone, Outcome.state] using
                  depthContext.callback body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) (ordinary_available afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
              have ordinaryCovered := InternedFreshOrdinaryCoverage.callback_covered body _ (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth
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
                      obtain ⟨origin, rooted, crossings, path, growth, traces⟩ := scope _ member
                      exact ⟨origin, rooted, smart, body, environment, state, depth, afterDepth, ordinary, crossings,
                        context, path, growth, traces, depthDone, ordinaryDone, depthAvailable, ordinaryAvailable,
                        rfl, ⟨entry, found⟩, stored⟩
              | none =>
                  let entry := Cache.intern afterOrdinary.nodes (muKey depth ordinary)
                  let allocated := {afterOrdinary with nodes := entry.2}
                  let crossing : Crossing Symbol Guard :=
                    ⟨smart, body, environment, state, .interned entry.1.identity, allocated, context,
                      .fresh depth ordinary afterDepth afterOrdinary depthDone ordinaryDone found⟩
                  obtain ⟨rawDepth, afterRawDepth, rawDepthDone, _⟩ := bind_done _ _ _ _ depthDone
                  let origin : Origin Symbol Guard (muKey depth ordinary) :=
                    ⟨smart, body, environment, state, rawDepth, afterRawDepth, depth, afterDepth, ordinary, afterOrdinary,
                      context, rawDepthDone, depthDone, ordinaryDone, rfl, found, ordinaryContext, depthAvailable, ordinaryAvailable⟩
                  have allocatedScope : Scoped root initial (muKey depth ordinary :: waiting) body
                      (.reference (.interned entry.1.identity) :: environment) allocated :=
                    Scoped.reserve origin reached (scope.enter crossing)
                  have allocatedCovered := reserve_covered (muKey depth ordinary) afterOrdinary ordinaryCovered
                  simp only [request, found] at pending
                  change (InternedFreshOrdinaryFacts.callback body environment (.interned entry.1.identity) allocated).bind _ = .pending key final at pending
                  cases bodyDone : InternedFreshOrdinaryFacts.callback body environment (.interned entry.1.identity) allocated with
                  | done value after => simp [bodyDone, Outcome.bind] at pending
                  | pending selected after =>
                      simp only [bodyDone, Outcome.bind, Outcome.pending.injEq] at pending
                      obtain ⟨rfl, rfl⟩ := pending
                      exact invoke (muKey depth ordinary :: waiting) _ allocated crossing.facts.1 allocatedCovered allocatedScope (Reached.enter crossing reached) _ _ bodyDone
termination_by sizeOf expression

/-- The stopped member of an ordered child list retains the source paths of all active ancestors. -/
theorem buildMany_encounter [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard)) (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment) (waiting : List NodeKey)
    (covered : Covered waiting state) (scope : ∀ expression ∈ expressions, Scoped root initial waiting expression environment state)
    (reached : ∀ expression ∈ expressions, Reached root initial expression environment state)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.buildMany expressions environment state = .pending key final) : Encounter root initial key final := by
  cases expressions with
  | nil => simp [InternedFreshOrdinaryConstruction.buildMany] at pending
  | cons first rest =>
      have firstVerified := InternedFreshOrdinaryFacts.build_verified first _ state context.normal.facts context.inputs
      cases firstDone : InternedFreshOrdinaryConstruction.build first environment state with
      | pending selected after =>
          simp only [InternedFreshOrdinaryConstruction.buildMany, firstDone, Outcome.bind, Outcome.pending.injEq] at pending
          obtain ⟨rfl, rfl⟩ := pending
          exact build_encounter root initial first environment state context waiting covered (scope first List.mem_cons_self) (reached first List.mem_cons_self) _ _ firstDone
      | done value after =>
          have afterContext : Context after environment := by simpa only [firstDone, Outcome.state] using context.build first
          have afterCovered := InternedFreshOrdinaryCoverage.build_covered first _ state context.normal.facts.coherent.valid covered value after firstDone
          have afterGrowth : Grows state after := by simpa only [firstDone, Outcome.state] using firstVerified.growth
          cases restDone : InternedFreshOrdinaryConstruction.buildMany rest environment after with
          | done values last => simp [InternedFreshOrdinaryConstruction.buildMany, firstDone, Outcome.bind, restDone] at pending
          | pending selected last =>
              simp only [InternedFreshOrdinaryConstruction.buildMany, firstDone, Outcome.bind, restDone, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              exact buildMany_encounter root initial rest environment after afterContext waiting afterCovered
                (fun expression member => (scope expression (List.mem_cons_of_mem first member)).grows afterGrowth)
                (fun expression member => (reached expression (List.mem_cons_of_mem first member)).grows afterGrowth) _ _ restDone
termination_by sizeOf expressions

/-- The stopped edge child retains actual source origins across all preceding child and edge effects. -/
theorem buildEdges_encounter [DecidableEq (EdgeKey Symbol Guard)]
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard)) (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment) (waiting : List NodeKey)
    (covered : Covered waiting state)
    (scope : ∀ symbol guard children, .mk symbol guard children ∈ expressions →
      ∀ expression ∈ children, Scoped root initial waiting expression environment state)
    (reached : ∀ symbol guard children, .mk symbol guard children ∈ expressions →
      ∀ expression ∈ children, Reached root initial expression environment state)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.buildEdges expressions environment state = .pending key final) : Encounter root initial key final := by
  cases expressions with
  | nil => simp [InternedFreshOrdinaryConstruction.buildEdges] at pending
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have childVerified := InternedFreshOrdinaryFacts.buildMany_verified children _ state context.normal.facts context.inputs
          cases childrenDone : InternedFreshOrdinaryConstruction.buildMany children environment state with
          | pending selected after =>
              simp only [InternedFreshOrdinaryConstruction.buildEdges, childrenDone, Outcome.bind, Outcome.pending.injEq] at pending
              obtain ⟨rfl, rfl⟩ := pending
              exact buildMany_encounter root initial children environment state context waiting covered
                (scope symbol constraint children List.mem_cons_self)
                (reached symbol constraint children List.mem_cons_self) _ _ childrenDone
          | done values after =>
              have afterContext : Context after environment := by simpa only [childrenDone, Outcome.state] using context.many children
              have afterCovered := InternedFreshOrdinaryCoverage.buildMany_covered children _ state context.normal.facts.coherent.valid covered values after childrenDone
              have afterGrowth : Grows state after := by simpa only [childrenDone, Outcome.state] using childVerified.growth
              let edge := run (makeEdge symbol constraint values) after
              have edgeVerified := edge_verified symbol constraint values after afterContext.normal.facts (childVerified.result _ _ childrenDone)
              have edgeContext : Context edge.2 environment := afterContext.edge symbol constraint values (childVerified.result _ _ childrenDone)
              have edgeCovered := run_covered (makeEdge symbol constraint values) after afterContext.normal.facts.coherent.valid afterCovered
              cases restDone : InternedFreshOrdinaryConstruction.buildEdges rest environment edge.2 with
              | done values last =>
                  simp only [InternedFreshOrdinaryConstruction.buildEdges, childrenDone, Outcome.bind, work] at pending
                  change (InternedFreshOrdinaryConstruction.buildEdges rest environment edge.2).bind _ = .pending key final at pending
                  simp [restDone, Outcome.bind] at pending
              | pending selected last =>
                  simp only [InternedFreshOrdinaryConstruction.buildEdges, childrenDone, Outcome.bind, work] at pending
                  change (InternedFreshOrdinaryConstruction.buildEdges rest environment edge.2).bind _ = .pending key final at pending
                  simp only [restDone, Outcome.bind, Outcome.pending.injEq] at pending
                  obtain ⟨rfl, rfl⟩ := pending
                  exact buildEdges_encounter root initial rest environment edge.2 edgeContext waiting edgeCovered
                    (fun s g c member expression included =>
                      (scope s g c (List.mem_cons_of_mem _ member) expression included).grows (grows_trans afterGrowth edgeVerified.growth))
                    (fun s g c member expression included =>
                      (reached s g c (List.mem_cons_of_mem _ member) expression included).grows (grows_trans afterGrowth edgeVerified.growth)) _ _ restDone
termination_by sizeOf expressions
end


/-- A complete initial heap derives the original source path of the encountered active reservation. -/
theorem complete_encounter [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (covered : Covered [] state) (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.build expression environment state = .pending key final) :
    Encounter expression environment key final :=
  build_encounter expression environment expression environment state context [] covered
    (by intro key member; cases member) (reached_initial expression environment state) key final pending

/-- Canonical readback retains the same origin and its original source path. -/
theorem complete_site [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (covered : Covered [] state) (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.build expression environment state = .pending key final) :
    ∃ origin : Origin Symbol Guard key, Rooted expression environment origin ∧
      Nonempty (InternedFreshOrdinaryActiveSite.Site origin final) := by
  obtain ⟨origin, rooted, atOrigin⟩ := complete_encounter expression environment state context covered key final pending
  exact ⟨origin, rooted, InternedFreshOrdinaryActiveSite.encounter_site_at origin final atOrigin⟩

/-- Actual pending execution retains the original source path and the live mismatch at the same exact origin. -/
theorem complete_mismatch [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (covered : Covered [] state) (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.build expression environment state = .pending key final) :
    ∃ origin : Origin Symbol Guard key, Rooted expression environment origin ∧
      ∃ site : InternedFreshOrdinaryActiveSite.Site origin final, InternedFreshOrdinaryJointMismatch.Mismatch site := by
  obtain ⟨origin, rooted, ⟨site⟩⟩ := complete_site expression environment state context covered key final pending
  exact ⟨origin, rooted, site, InternedFreshOrdinaryJointMismatch.Site.mismatch site⟩

/-- Closed repaired pending execution derives actual shorter producers for every ordinary capture in its ancestor Depth probe. -/
theorem closed_mismatch_producers [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard)
    (pending : InternedFreshOrdinaryConstruction.build expression [] empty = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : InternedFreshOrdinaryActiveSite.Site origin final,
      InternedFreshOrdinaryJointMismatch.Mismatch site ∧
      ∀ level, .uninterned level ∈ origin.depth.free → ProducedAt (.binder origin.smart origin.body) origin.environment origin.before level := by
  obtain ⟨origin, rooted, site, mismatch⟩ :=
    complete_mismatch expression [] empty InternedFreshOrdinaryContext.empty_context empty_correct.2 key final pending
  refine ⟨origin, site, mismatch, ?_⟩
  intro level member
  rcases Rooted.ordinary_capture rooted level member with ⟨original, impossible, _⟩ | produced
  · cases impossible
  · exact produced

end MicroCFTA.InternedFreshOrdinaryRootEncounter
