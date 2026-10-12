import MicroCFTA.InternedNestedConstructionGrowth

/-!
# Exact replay derived from arbitrary nested constructor syntax

Every successful complete execution replays its exact record after table
growth. Probe computations replay by syntax induction. A completed Mu key
then returns its canonical payload without reevaluating its stored body.
-/
namespace MicroCFTA.InternedNestedConstruction
open Cache InternedConstructorTemplates
open InternedBinderProtocol (Reference NodeKey)

/-- A complete execution can be read back after all of its original tables have grown. -/
def Replays (execute : InternedConstructorTemplates.State Symbol Guard → Outcome Symbol Guard Result) : Prop :=
  ∀ before after value final, InternedConstructorTemplates.Valid before → execute before = .done value final →
    Grows final after → execute after = .done value after

/-- Every prefix retains the canonical state needed to replay its later source effects. -/
def Growing (execute : InternedConstructorTemplates.State Symbol Guard → Outcome Symbol Guard Result) : Prop :=
  ∀ state, InternedConstructorTemplates.Valid state →
    InternedConstructorTemplates.Valid (execute state).state ∧ Grows state (execute state).state

/-- A pure source result has no cache effects to repeat. -/
theorem pure_replays (value : Result) : Replays (Symbol := Symbol) (Guard := Guard) (fun state => .done value state) := by
  intro before after actual final _ same _
  cases same
  rfl

/-- The existing finite constructor replay theorem supplies the ordinary effect case. -/
theorem work_replays [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result) :
    Replays (work computation) := by
  intro before after value final valid returned growth
  cases original : run computation before with
  | mk result state =>
      simp only [work, original, Outcome.done.injEq] at returned
      rcases returned with ⟨rfl, rfl⟩
      have again := InternedConstructorTemplates.replay computation before after valid (by simpa only [original] using growth)
      simp only [work, again, original]

/-- Sequential replay derives each intermediate result and then repeats the exact continuation. -/
theorem bind_replays
    (first : InternedConstructorTemplates.State Symbol Guard → Outcome Symbol Guard First)
    (next : First → InternedConstructorTemplates.State Symbol Guard → Outcome Symbol Guard Result)
    (firstGrowing : Growing first) (nextGrowing : ∀ value, Growing (next value))
    (firstReplay : Replays first) (nextReplay : ∀ value, Replays (next value)) :
    Replays (fun state => (first state).bind next) := by
  intro before after value final valid returned growth
  cases firstResult : first before with
  | pending key state => simp [firstResult, Outcome.bind] at returned
  | done head middle =>
      have middleValid : InternedConstructorTemplates.Valid middle := by
        simpa only [firstResult, Outcome.state] using (firstGrowing before valid).1
      have tail : next head middle = .done value final := by simpa only [firstResult, Outcome.bind] using returned
      have tailGrowth : Grows middle final := by
        simpa only [tail, Outcome.state] using (nextGrowing head middle middleValid).2
      change (first after).bind next = _
      rw [firstReplay before after head middle valid firstResult (grows_trans tailGrowth growth)]
      exact nextReplay head middle after value final middleValid tail growth

/-- The actual post-probe request preserves state validity for any locally growing body execution. -/
theorem request_correct [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → InternedConstructorTemplates.State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (callbackGrowing : ∀ name, Growing (callback name)) : Growing (request smart depth ordinary callback) := by
  intro state valid
  simp only [request]
  split
  · split <;> exact ⟨valid, grows_refl _⟩
  · let key := muKey depth ordinary
    let entry := Cache.intern state.nodes key
    let allocated := {state with nodes := entry.2}
    have allocatedValid : InternedConstructorTemplates.Valid allocated :=
      ⟨valid.1, (Cache.intern_correct _ _ valid.2).1⟩
    have allocatedGrowth : Grows state allocated :=
      ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
    apply bind_correct _ _ state
    · have body := callbackGrowing (.interned entry.1.identity) allocated allocatedValid
      exact ⟨body.1, grows_trans allocatedGrowth body.2⟩
    · intro body afterBody bodyValid
      exact ⟨bodyValid, ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩⟩

/-- A completed canonical request replays without any body replay or key stability assumption. -/
theorem request_replays [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → InternedConstructorTemplates.State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (callbackGrowing : ∀ name, Growing (callback name)) : Replays (request smart depth ordinary callback) := by
  intro before after value final valid returned growth
  cases found : before.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases stored : before.nodeRecords (muKey depth ordinary) with
      | none => simp [request, found, stored] at returned
      | some original =>
          simp only [request, found, stored, Outcome.done.injEq] at returned
          rcases returned with ⟨rfl, rfl⟩
          simp only [request, growth.nodes _ _ found, growth.nodeRecords _ _ stored]
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern before.nodes key
      let allocated := {before with nodes := entry.2}
      have allocatedValid : InternedConstructorTemplates.Valid allocated :=
        ⟨valid.1, (Cache.intern_correct _ _ valid.2).1⟩
      cases bodyResult : callback (.interned entry.1.identity) allocated with
      | pending pending state =>
          simp only [request, found] at returned
          change (callback (.interned entry.1.identity) allocated).bind _ = _ at returned
          simp [bodyResult, Outcome.bind] at returned
      | done body bodyState =>
          let candidate := Value.mu entry.1 body depth ordinary
          let completed := {bodyState with nodeRecords := keepFirst bodyState.nodeRecords key candidate}
          obtain ⟨record, present⟩ := keepFirst_present bodyState.nodeRecords key candidate
          have done : request smart depth ordinary callback before = .done (finish smart record) completed := by
            simp only [request, found]
            change (callback (.interned entry.1.identity) allocated).bind _ = _
            simp only [bodyResult, Outcome.bind]
            change Outcome.done (finish smart ((keepFirst bodyState.nodeRecords key candidate key).getD candidate)) completed = _
            rw [present]
            rfl
          rw [done] at returned
          obtain ⟨sameValue, sameFinal⟩ := Outcome.done.inj returned
          rw [← sameFinal] at growth
          rw [← sameValue]
          have bodyGrowth : Grows allocated bodyState := by
            simpa only [bodyResult, Outcome.state] using (callbackGrowing (.interned entry.1.identity) allocated allocatedValid).2
          have installed : completed.nodes.table key = some entry.1 :=
            bodyGrowth.nodes key entry.1 (Cache.intern_correct before.nodes key valid.2).2.1
          have visible : after.nodeRecords key = some record := growth.nodeRecords key record present
          have canonical : after.nodes.table key = some entry.1 := growth.nodes key entry.1 installed
          dsimp only [key] at canonical visible
          simp only [request, canonical, visible]

mutual
/-- Successful nested source programs derive complete exact replay from their finite syntax. -/
theorem build_replays [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) : Replays (build expression environment) := by
  change Replays (fun state => build expression environment state)
  cases expression with
  | empty => simpa only [build] using (pure_replays (Symbol := Symbol) (Guard := Guard) Value.empty)
  | var index => simpa only [build] using (pure_replays (environment[index]?.getD Value.empty))
  | node edges =>
      simpa only [build] using bind_replays (buildEdges edges environment)
        (fun values state => work (makeNode values) state)
        (buildEdges_correct edges environment) (fun values => work_correct (makeNode values))
        (buildEdges_replays edges environment) (fun values => work_replays (makeNode values))
  | union members =>
      simpa only [build] using bind_replays (buildMany members environment)
        (fun values state => work (makeUnion values) state)
        (buildMany_correct members environment) (fun values => work_correct (makeUnion values))
        (buildMany_replays members environment) (fun values => work_replays (makeUnion values))
  | binder smart body =>
      simp only [build]
      let callback := fun name state => (build body (.reference name :: environment) state).bind
        fun value next => work (withoutSelfReference name value) next
      have callbackGrowing : ∀ name, Growing (callback name) := by
        intro name state valid
        exact bind_correct _ _ state (build_correct body _ state valid)
          (fun value next valid => work_correct (withoutSelfReference name value) next valid)
      have callbackReplay : ∀ name, Replays (callback name) := by
        intro name
        exact bind_replays (build body (.reference name :: environment))
          (fun value state => work (withoutSelfReference name value) state)
          (build_correct body _) (fun value => work_correct (withoutSelfReference name value))
          (build_replays body _) (fun value => work_replays (withoutSelfReference name value))
      change Replays (fun state => (callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary)
      apply bind_replays _ _ (callbackGrowing .depth)
      · intro depth state valid
        exact bind_correct _ _ state (callbackGrowing (.uninterned depth.depth) state valid)
          (fun ordinary => request_correct smart depth ordinary callback callbackGrowing)
      · exact callbackReplay .depth
      · intro depth
        exact bind_replays (callback (.uninterned depth.depth))
          (fun ordinary state => request smart depth ordinary callback state)
          (callbackGrowing (.uninterned depth.depth))
          (fun ordinary => request_correct smart depth ordinary callback callbackGrowing)
          (callbackReplay (.uninterned depth.depth))
          (fun ordinary => request_replays smart depth ordinary callback callbackGrowing)
termination_by sizeOf expression

/-- Every child result and complete list replays in its original source order. -/
theorem buildMany_replays [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) : Replays (buildMany expression environment) := by
  change Replays (fun state => buildMany expression environment state)
  cases expression with
  | nil => simpa only [buildMany] using (pure_replays (Symbol := Symbol) (Guard := Guard) ([] : List (Value Symbol Guard)))
  | cons first rest =>
      simp only [buildMany]
      apply bind_replays _ _ (build_correct first environment)
      · intro value state valid
        exact bind_correct _ _ state (buildMany_correct rest environment state valid)
          (fun values final valid => ⟨valid, grows_refl _⟩)
      · exact build_replays first environment
      · intro value
        exact bind_replays (buildMany rest environment) (fun values final => .done (value :: values) final)
          (buildMany_correct rest environment) (fun values state valid => ⟨valid, grows_refl _⟩)
          (buildMany_replays rest environment) (fun values => pure_replays (value :: values))
termination_by sizeOf expression

/-- Nested edge construction reuses its ordered canonical child records and complete edge payloads. -/
theorem buildEdges_replays [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) : Replays (buildEdges expression environment) := by
  change Replays (fun state => buildEdges expression environment state)
  cases expression with
  | nil => simpa only [buildEdges] using (pure_replays (Symbol := Symbol) (Guard := Guard) ([] : List (EdgeValue Symbol Guard)))
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges]
          apply bind_replays _ _ (buildMany_correct children environment)
          · intro values state valid
            apply bind_correct _ _ state (work_correct (makeEdge symbol constraint values) state valid)
            intro edge afterEdge edgeValid
            exact bind_correct _ _ afterEdge (buildEdges_correct rest environment afterEdge edgeValid)
              (fun edges final valid => ⟨valid, grows_refl _⟩)
          · exact buildMany_replays children environment
          · intro values
            apply bind_replays _ _ (work_correct (makeEdge symbol constraint values))
            · intro edge state valid
              exact bind_correct _ _ state (buildEdges_correct rest environment state valid)
                (fun edges final valid => ⟨valid, grows_refl _⟩)
            · exact work_replays (makeEdge symbol constraint values)
            · intro edge
              exact bind_replays (buildEdges rest environment) (fun edges final => .done (edge :: edges) final)
                (buildEdges_correct rest environment) (fun edges state valid => ⟨valid, grows_refl _⟩)
                (buildEdges_replays rest environment) (fun edges => pure_replays (edge :: edges))
termination_by sizeOf expression
end

/-- Arbitrary complete nested construction replays its exact immutable record with no new allocation. -/
theorem build_replay [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before after : InternedConstructorTemplates.State Symbol Guard)
    (value : Value Symbol Guard) (final : InternedConstructorTemplates.State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before) (completed : build expression environment before = .done value final)
    (growth : Grows final after) : build expression environment after = .done value after :=
  build_replays expression environment before after value final valid completed growth

/-- Empty-cache completion supplies the source validity premise without an external assumption. -/
theorem empty_replay [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (final after : InternedConstructorTemplates.State Symbol Guard)
    (completed : build expression [] empty = .done value final) (growth : Grows final after) :
    build expression [] after = .done value after :=
  build_replay expression [] empty after value final empty_valid completed growth

end MicroCFTA.InternedNestedConstruction
