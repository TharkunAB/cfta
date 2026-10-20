import MicroCFTA.InternedNestedConstructionReplay
import MicroCFTA.InternedFreshOrdinaryGrowth
import MicroCFTA.InternedFreshOrdinaryFacts

/-!
# Exact replay of completed repaired constructor programs

Successful complete executions replay their original values after cache growth.
Both probes use the repaired chooser. A complete canonical request reuses its
stored body, so replay requires no body equality assumption or semantic heap.
-/
namespace MicroCFTA.InternedFreshOrdinaryReplay
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request Replays Growing
  pure_replays work_replays bind_replays bind_correct work_correct request_correct request_replays)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryGrowth InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)

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
        (callback (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary)
      apply bind_replays _ _ (callbackGrowing .depth)
      · intro depth state valid
        exact bind_correct _ _ state (callbackGrowing (.uninterned (ordinaryLevel depth)) state valid)
          (fun ordinary => request_correct smart depth ordinary callback callbackGrowing)
      · exact callbackReplay .depth
      · intro depth
        exact bind_replays (callback (.uninterned (ordinaryLevel depth)))
          (fun ordinary state => request smart depth ordinary callback state)
          (callbackGrowing (.uninterned (ordinaryLevel depth)))
          (fun ordinary => request_correct smart depth ordinary callback callbackGrowing)
          (callbackReplay (.uninterned (ordinaryLevel depth)))
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

/-- A completed repaired callback also replays its exact normalized observation. -/
theorem callback_replays [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) : Replays (callback expression environment name) :=
  bind_replays (build expression (.reference name :: environment))
    (fun value state => work (withoutSelfReference name value) state)
    (build_correct expression _) (fun value => work_correct (withoutSelfReference name value))
    (build_replays expression _) (fun value => work_replays (withoutSelfReference name value))

end MicroCFTA.InternedFreshOrdinaryReplay
