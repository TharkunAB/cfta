import MicroCFTA.InternedSpecialKeyReadiness

/-!
# Actual pending source encounters retain their profile context

The witness gives the exact source body, literal lexical inputs, both
completed normalized probe calls, and the verified cache state before
the first call. The witness does not assume that the run completes.
-/
namespace MicroCFTA.InternedProfilePendingEncounter
open Cache InternedConstructorTemplates InternedNestedConstruction InternedNestedSpecialization
open InternedNestedMissReadback InternedProbeProvenance InternedNestedProvenance
open InternedStoredMuOrigins InternedProfileTraceSites InternedSpecialKeyReadiness
open InternedBinderProtocol (Reference NodeKey)

/-- The stopped request has an actual source body and two complete profile-verified probe calls. -/
def Encounter [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (final : State Symbol Guard) : Prop :=
  ∃ body, ∃ names : List Reference, ∃ before depth afterDepth ordinary,
    Context before (names.map Value.reference) ∧
    callback body (names.map Value.reference) .depth before = .done depth afterDepth ∧
    callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary final ∧
    key = muKey depth ordinary ∧ IsPending key final

/-- Every pending branch in this outcome has a verified actual source encounter. -/
def Reports [DecidableEq (EdgeKey Symbol Guard)] (outcome : Outcome Symbol Guard Result) : Prop :=
  ∀ key final, outcome = .pending key final → Encounter key final

/-- A completed source action has no pending branch to report. -/
theorem reports_done [DecidableEq (EdgeKey Symbol Guard)] (value : Result) (state : State Symbol Guard) : Reports (.done value state) := by
  intro key final same
  cases same

/-- Source sequencing reports either its stopped prefix or its stopped continuation. -/
theorem bind_reports [DecidableEq (EdgeKey Symbol Guard)] (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : Reports outcome)
    (later : ∀ value after, outcome = .done value after → Reports (next value after)) : Reports (outcome.bind next) := by
  cases outcome with
  | pending name state =>
      intro key final same
      have equal := Outcome.pending.inj same
      exact first key final (by rw [equal.1, equal.2])
  | done value state => exact later value state rfl

mutual
/-- Full syntax derives the exact profile prefix of each actual pending readback. -/
theorem build_reports [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference)) :
    Reports (build expression (names.map Value.reference) state) := by
  cases expression with
  | empty | var index => simpa only [build] using reports_done _ _
  | node edges =>
      rw [build]
      apply bind_reports _ _ (buildEdges_reports edges names state context)
      intro values after completed
      exact reports_done _ _
  | union members =>
      rw [build]
      apply bind_reports _ _ (buildMany_reports members names state context)
      intro values after completed
      exact reports_done _ _
  | binder smart body =>
      have invoke : ∀ name current, Context current (names.map Value.reference) →
          Available current (.reference name) → Reports (callback body (names.map Value.reference) name current) := by
        intro name current currentContext argument
        have localContext : Context current ((name :: names).map Value.reference) := by
          refine ⟨currentContext.normal, ?_, currentContext.heap⟩
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact argument
          · exact currentContext.inputs value member
        apply bind_reports _ _ (build_reports body (name :: names) current localContext)
        intro value after completed
        exact reports_done _ _
      rw [build]
      change Reports ((callback body (names.map Value.reference) .depth state).bind fun depth afterDepth =>
        (callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body (names.map Value.reference)) afterOrdinary)
      apply bind_reports _ _ (invoke .depth state context (depth_available state))
      intro depth afterDepth depthDone
      have depthContext : Context afterDepth (names.map Value.reference) := by
        simpa only [depthDone, Outcome.state] using InternedSpecialKeyReadiness.Context.callback context body .depth (depth_available state)
      apply bind_reports _ _ (invoke (.uninterned depth.depth) afterDepth depthContext (ordinary_available afterDepth depth.depth))
      intro ordinary afterOrdinary ordinaryDone
      have ordinaryContext : Context afterOrdinary (names.map Value.reference) := by
        simpa only [ordinaryDone, Outcome.state] using InternedSpecialKeyReadiness.Context.callback depthContext body (.uninterned depth.depth) (ordinary_available afterDepth depth.depth)
      cases found : afterOrdinary.nodes.table (muKey depth ordinary) with
      | some entry =>
          cases stored : afterOrdinary.nodeRecords (muKey depth ordinary) with
          | some record => simpa only [request, found, stored] using reports_done (finish smart record) afterOrdinary
          | none =>
              intro key final stopped
              simp only [request, found, stored, Outcome.pending.injEq] at stopped
              rcases stopped with ⟨rfl, rfl⟩
              exact ⟨body, names, state, depth, afterDepth, ordinary, context, depthDone, ordinaryDone, rfl, ⟨entry, found⟩, stored⟩
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
          simp only [request, found]
          change Reports ((callback body (names.map Value.reference) (.interned entry.1.identity) allocated).bind _)
          apply bind_reports _ _ (invoke _ allocated allocatedContext argument)
          intro value after completed
          exact reports_done _ _
termination_by sizeOf expression

/-- An ordered child traversal retains the actual context at its stopped child. -/
theorem buildMany_reports [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference)) :
    Reports (buildMany expressions (names.map Value.reference) state) := by
  cases expressions with
  | nil => simpa only [buildMany] using reports_done _ _
  | cons first rest =>
      rw [buildMany]
      apply bind_reports _ _ (build_reports first names state context)
      intro value after completed
      have afterContext : Context after (names.map Value.reference) := by
        simpa only [completed, Outcome.state] using context.build first
      apply bind_reports _ _ (buildMany_reports rest names after afterContext)
      intro values final completedRest
      exact reports_done _ _
termination_by sizeOf expressions

/-- Edge allocation preserves the exact profile context for later source children. -/
theorem buildEdges_reports [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference)) :
    Reports (buildEdges expressions (names.map Value.reference) state) := by
  cases expressions with
  | nil => simpa only [buildEdges] using reports_done _ _
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_reports _ _ (buildMany_reports children names state context)
          intro values after completed
          have afterContext : Context after (names.map Value.reference) := by
            simpa only [completed, Outcome.state] using context.many children
          have available := (buildMany_verified children (names.map Value.reference) state context.normal.facts context.inputs).result values after completed
          apply bind_reports _ _ (reports_done _ _)
          intro edge afterEdge edgeDone
          have exactEdge : work (makeEdge symbol constraint values) after = .done edge afterEdge := edgeDone
          have edgeContext : Context afterEdge (names.map Value.reference) := by
            have current := afterContext.edge symbol constraint values available
            change Context (work (makeEdge symbol constraint values) after).state _ at current
            simpa only [exactEdge, Outcome.state] using current
          apply bind_reports _ _ (buildEdges_reports rest names afterEdge edgeContext)
          intro edges final restDone
          exact reports_done _ _
termination_by sizeOf expressions
end

/-- A closed first source execution derives every required historical profile premise at its actual stopped call. -/
theorem closed_encounter [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) (stopped : build expression [] empty = .pending key final) :
    Encounter key final := by
  apply build_reports expression [] empty ?_ key final stopped
  exact ⟨empty_normal, (by intro value member; cases member), InternedProfileHeap.empty_heap⟩

end MicroCFTA.InternedProfilePendingEncounter
