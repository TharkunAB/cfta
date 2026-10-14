import MicroCFTA.SourceRecursiveIntersectionMaybeMu
import MicroCFTA.InternedFreshOrdinaryCoverage

/-!
# Payload coverage of actual optional-binder effects

Actual stored substitution and normalized callbacks retain prior payload
coverage on successful return. This includes arbitrary open nested bodies.
The result does not assume that a callback completes. Cache validity holds
at both returned and pending outcomes.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMaybeMu
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedNestedConstruction (Outcome work request bind_correct work_correct)
open InternedNestedCoverage (OnDone bind_covered work_covered request_covered)
open InternedBinderProtocol (Reference)

/-- Actual source callbacks retain cache validity and physical record growth for both outcomes. -/
theorem callback_correct [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (state : State Symbol Guard) (valid : Valid state) :
    Valid (callback old body name state).state ∧ Grows state (callback old body name state).state := by
  unfold callback InternedFreshOrdinaryStoredSubstitution.execute
  exact bind_correct _ _ state (InternedFreshOrdinaryGrowth.build_correct _ _ state valid)
    (fun value after afterValid => work_correct (withoutSelfReference name value) after afterValid)

/-- A completed actual callback retains all original payload coverage through arbitrary nested substitution. -/
theorem callback_covered [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (state : State Symbol Guard) (valid : Valid state) (covered : Covered pending state) :
    OnDone pending (callback old body name state) := by
  have checked : Valid (InternedFreshOrdinaryStoredSubstitution.execute body
      (InternedStoredSubstitutionRebind.replacement old (.reference name)) state).state :=
    (InternedFreshOrdinaryGrowth.build_correct _ _ state valid).1
  unfold callback InternedFreshOrdinaryStoredSubstitution.execute at *
  apply bind_covered pending pending _ _ (InternedFreshOrdinaryCoverage.build_covered _ _ state valid covered)
  intro value after done afterCovered
  have afterValid : Valid after := by
    simpa only [done, Outcome.state] using checked
  exact work_covered (withoutSelfReference name value) after afterValid afterCovered

/-- Both actual probes and the canonical binder request retain valid caches on either outcome. -/
theorem construct_correct [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) (valid : Valid state) :
    Valid (construct old body state).state ∧ Grows state (construct old body state).state := by
  unfold construct
  apply bind_correct _ _ state (callback_correct old body .depth state valid)
  intro depth afterDepth depthValid
  apply bind_correct _ _ afterDepth
    (callback_correct old body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthValid)
  intro ordinary afterOrdinary ordinaryValid
  cases installed : afterOrdinary.nodes.table (muKey depth ordinary) with
  | some entry =>
    cases stored : afterOrdinary.nodeRecords (muKey depth ordinary) <;>
      simp only [request, installed, stored, Outcome.state] <;> exact ⟨ordinaryValid, grows_refl _⟩
  | none =>
    simp only [request, installed]
    let key := muKey depth ordinary
    let entry := Cache.intern afterOrdinary.nodes key
    let allocated := {afterOrdinary with nodes := entry.2}
    have allocatedValid : Valid allocated := ⟨ordinaryValid.1, (Cache.intern_correct _ _ ordinaryValid.2).1⟩
    have allocatedGrowth : Grows afterOrdinary allocated :=
      ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
    apply bind_correct _ _ afterOrdinary
    · have actual := callback_correct old body (.interned entry.1.identity) allocated allocatedValid
      exact ⟨actual.1, grows_trans allocatedGrowth actual.2⟩
    · intro value after afterValid
      exact ⟨afterValid, ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩⟩

/-- Every completed actual binder restores the incoming payload coverage after its own reservation. -/
theorem construct_covered [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) (valid : Valid state) (covered : Covered pending state) :
    OnDone pending (construct old body state) := by
  unfold construct
  apply bind_covered pending pending _ _ (callback_covered old body .depth state valid covered)
  intro depth afterDepth depthDone depthCovered
  have depthValid : Valid afterDepth := by simpa only [depthDone, Outcome.state] using (callback_correct old body .depth state valid).1
  let name := Reference.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)
  apply bind_covered pending pending _ _ (callback_covered old body name afterDepth depthValid depthCovered)
  intro ordinary afterOrdinary ordinaryDone ordinaryCovered
  have ordinaryValid : Valid afterOrdinary := by
    simpa only [ordinaryDone, Outcome.state] using (callback_correct old body name afterDepth depthValid).1
  exact request_covered true depth ordinary (callback old body) afterOrdinary ordinaryValid ordinaryCovered
    (fun _ name current currentValid currentCovered => callback_covered old body name current currentValid currentCovered)

/-- Optional source binding retains valid caches and physical growth on either actual outcome. -/
theorem maybeMu_correct [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (valid : Valid state) :
    Valid (maybeMu key body state).state ∧ Grows state (maybeMu key body state).state := by
  unfold maybeMu
  split
  · exact construct_correct _ body state valid
  · exact ⟨valid, grows_refl _⟩

/-- A completed optional binder preserves complete coverage without a body-preparation premise. -/
theorem maybeMu_covered [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (valid : Valid state) (covered : Covered pending state) :
    OnDone pending (maybeMu key body state) := by
  unfold maybeMu
  split
  · exact construct_covered _ body state valid covered
  · intro value after done
    cases done
    exact covered

end MicroCFTA.SourceRecursiveIntersectionMaybeMu
