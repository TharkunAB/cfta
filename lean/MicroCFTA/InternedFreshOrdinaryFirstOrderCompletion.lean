import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedFreshOrdinaryGrowth
import MicroCFTA.InternedNestedCoverage

/-!
# Repaired first-run completion for one binder with arbitrary finite body syntax

The body can contain arbitrary constructor trees, unions, and captured values.
It contains no nested binder request. Each actual probe and fresh body call
therefore completes. Existing cache hits require complete payload coverage.
The proof retains the selected fresh ordinary name and all actual effects.
-/
namespace MicroCFTA.InternedFreshOrdinaryFirstOrderCompletion
open InternedConstructorTemplates InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome work request)
open InternedStoredShallowCompletion InternedNestedCoverage
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference)

/-- Each actual normalized body callback completes, even during an unfinished outer reservation. -/
theorem callback_complete [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (free : BinderFree body) (environment : List (Value Symbol Guard)) (name : Reference)
    (state : State Symbol Guard) :
    ∃ value final, callback body environment name state = .done value final := by
  obtain ⟨value, after, done⟩ := InternedStoredShallowCompletion.build_complete body
    (.reference name :: environment) state free
  have current : build body (.reference name :: environment) state = .done value after :=
    (InternedFreshOrdinaryStoredSubstitution.build_eq body _ state free).trans done
  exact ⟨(run (withoutSelfReference name value) after).1,
    (run (withoutSelfReference name value) after).2,
    by simp only [callback, current, Outcome.bind, work]⟩

/-- Binder-free callbacks preserve payload coverage at their actual returned cache. -/
theorem callback_covered [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (free : BinderFree body) (environment : List (Value Symbol Guard)) (name : Reference)
    (state : State Symbol Guard) (valid : Valid state) (covered : InternedRecordCoherence.Covered pending state) :
    OnDone pending (callback body environment name state) := by
  unfold callback
  rw [InternedFreshOrdinaryStoredSubstitution.build_eq body _ state free]
  apply bind_covered pending pending _ _
    (InternedNestedCoverage.build_covered body _ state valid covered)
  intro value after done coverage
  have afterValid : Valid after := by
    simpa only [done, Outcome.state] using
      (InternedNestedConstruction.build_correct body (.reference name :: environment) state valid).1
  exact work_covered (withoutSelfReference name value) after afterValid coverage

/-- The actual probe sequence derives coverage for both hit and fresh-body branches. -/
theorem binder_complete [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (free : BinderFree body) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : Valid state) (covered : InternedRecordCoherence.Covered [] state) :
    ∃ value final, build (.binder smart body) environment state = .done value final := by
  obtain ⟨depth, afterDepth, depthDone⟩ := callback_complete body free environment .depth state
  have depthCoverage := callback_covered body free environment .depth state valid covered depth afterDepth depthDone
  have expanded : build (.binder smart body) environment state =
      (callback body environment .depth state).bind fun depth afterDepth =>
      (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
        request smart depth ordinary (callback body environment) afterOrdinary := by
    rw [build]
    rfl
  have depthValid : Valid afterDepth := by
    have growth := InternedFreshOrdinaryGrowth.build_correct body (.reference .depth :: environment) state valid
    have filtered := InternedNestedConstruction.bind_correct _ _ state growth
      (fun value after valid => InternedNestedConstruction.work_correct (withoutSelfReference .depth value) after valid)
    have filteredValid := filtered.1
    change Valid (callback body environment .depth state).state at filteredValid
    simpa only [depthDone, Outcome.state] using filteredValid
  obtain ⟨ordinary, afterOrdinary, ordinaryDone⟩ :=
    callback_complete body free environment (.uninterned (ordinaryLevel depth)) afterDepth
  have ordinaryCoverage := callback_covered body free environment (.uninterned (ordinaryLevel depth))
    afterDepth depthValid depthCoverage ordinary afterOrdinary ordinaryDone
  rw [expanded, depthDone]
  simp only [Outcome.bind, ordinaryDone]
  cases installed : afterOrdinary.nodes.table (muKey depth ordinary) with
  | some entry =>
      rcases ordinaryCoverage.nodes _ entry installed with pending | ⟨record, stored⟩
      · cases pending
      · simp only [request, installed, stored]
        exact ⟨_, _, rfl⟩
  | none =>
      let entry := Cache.intern afterOrdinary.nodes (muKey depth ordinary)
      let allocated := {afterOrdinary with nodes := entry.2}
      obtain ⟨actual, afterBody, bodyDone⟩ := callback_complete body free environment (.interned entry.1.identity) allocated
      simp only [request, installed]
      change ∃ value final, (callback body environment (.interned entry.1.identity) allocated).bind _ = .done value final
      rw [bodyDone]
      exact ⟨_, _, rfl⟩

/-- Empty-cache first-order construction completes without a supplied successful run. -/
theorem closed_complete [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (free : BinderFree body) :
    ∃ value final, build (.binder smart body) [] empty = .done value final :=
  binder_complete smart body free [] empty empty_valid InternedRecordCoherence.empty_correct.2

/-- Actual completion derives the coherent returned payload and both cache histories. -/
theorem closed_verified_complete [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (free : BinderFree body) :
    ∃ value final, build (.binder smart body) [] empty = .done value final ∧
      Facts final ∧ InternedProbeProvenance.Available final value ∧ Grows empty final ∧
      Cache.Extends (empty (Symbol := Symbol) (Guard := Guard)).nodes.issued final.nodes.issued := by
  obtain ⟨value, final, done⟩ := closed_complete smart body free
  have checked := InternedFreshOrdinaryFacts.closed_verified (.binder smart body)
  exact ⟨value, final, done,
    by simpa only [done, Outcome.state] using checked.facts,
    checked.result value final done,
    by simpa only [done, Outcome.state] using checked.growth,
    by simpa only [done, Outcome.state] using checked.history⟩

end MicroCFTA.InternedFreshOrdinaryFirstOrderCompletion
