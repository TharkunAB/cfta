import MicroCFTA.InternedStoredSubstitutionRebind
import MicroCFTA.InternedFreshOrdinaryFirstOrderCompletion
import MicroCFTA.InternedFreshOrdinaryReplay
import MicroCFTA.SourceRecursiveIntersectionControl

/-!
# Actual recursive intersection binder construction

The source callback substitutes the repeated-pair reference in the stored
body. It then removes the callback's own direct union reference. Construction
keeps both probes, the selected fresh ordinary name, reservation, and cleanup.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMaybeMu
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Syntax Outcome work request)
open InternedStoredSubstitution InternedStoredSubstitutionRebind
open InternedBinderProtocol (Reference)

/-- The source substitutes the actual old pair name before callback normalization. -/
def callback [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  (InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference name)) state).bind
    fun value after => work (withoutSelfReference name value) after

/-- Source Mu construction performs the two actual normalized probes before its canonical request. -/
def construct [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  (callback old body .depth state).bind fun depth afterDepth =>
  (callback old body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth).bind
    fun ordinary afterOrdinary => request true depth ordinary (callback old body) afterOrdinary

/-- Source intersection constructs a binder only when its exact pair name remains free. -/
def maybeMu [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  if Reference.intersection key.1 key.2 ∈ body.free then construct (.intersection key.1 key.2) body state
  else .done body state

/-- Each actual source substitution callback equals the repaired lexical callback at every current cache. -/
theorem callback_eq [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (source current : State Symbol Guard) (facts : Facts source) (available : Available source body) :
    callback old body name current =
      InternedFreshOrdinaryFacts.callback (encode (leaves body) [old] body) (leaves body) name current := by
  unfold callback InternedFreshOrdinaryFacts.callback
  rw [rebind_build body old name source current facts.coherent available]

/-- Exact compilation retains source probes, fresh-name selection, hit/pending branches, reservation, and final cache. -/
theorem construct_eq [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (source current : State Symbol Guard) (facts : Facts source) (available : Available source body) :
    construct old body current =
      InternedFreshOrdinaryConstruction.build (.binder true (encode (leaves body) [old] body)) (leaves body) current := by
  have callbacks : callback old body = InternedFreshOrdinaryFacts.callback (encode (leaves body) [old] body) (leaves body) := by
    funext name state
    exact callback_eq old body name source state facts available
  simp only [construct, callbacks, InternedFreshOrdinaryFacts.callback, InternedFreshOrdinaryConstruction.build]
  rfl

/-- The complete source optional-binder call equals the repaired executor, including pending outcomes. -/
theorem maybeMu_eq [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (source current : State Symbol Guard) (facts : Facts source) (available : Available source body) :
    maybeMu key body current =
      if Reference.intersection key.1 key.2 ∈ body.free then
        InternedFreshOrdinaryConstruction.build
          (.binder true (encode (leaves body) [.intersection key.1 key.2] body)) (leaves body) current
      else .done body current := by
  unfold maybeMu
  split
  · exact construct_eq _ body source current facts available
  · rfl

/-- Every actual optional-binder outcome preserves complete source facts and both physical histories. -/
theorem verified [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state body) :
    Verified state (maybeMu key body state) Available := by
  rw [maybeMu_eq key body state state facts available]
  split
  · exact InternedFreshOrdinaryFacts.build_verified _ _ state facts (leaves_available body state available)
  · exact pure_verified state facts body Available available

/-- An unused recursive pair returns the literal existing record without constructor effects. -/
theorem unused [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (absent : Reference.intersection key.1 key.2 ∉ body.free) :
    maybeMu key body state = .done body state := by simp only [maybeMu, absent, ite_false]

/-- Prepared source callbacks complete even while another canonical request remains unfinished. -/
theorem callback_complete [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (source current : State Symbol Guard) (facts : Facts source) (available : Available source body)
    (prepared : InternedStoredClosedMuCompletion.PreparedWithoutMu body) :
    ∃ value final, callback old body name current = .done value final := by
  rw [callback_eq old body name source current facts available]
  exact InternedFreshOrdinaryFirstOrderCompletion.callback_complete _
    (InternedStoredClosedMuCompletion.encode_withoutMu _ _ body prepared) _ name current

/-- Actual prepared source probes derive their complete values, caches, and next canonical request. -/
theorem probes_complete [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (source current : State Symbol Guard) (facts : Facts source) (available : Available source body)
    (prepared : InternedStoredClosedMuCompletion.PreparedWithoutMu body) :
    ∃ depth afterDepth ordinary afterOrdinary,
      callback old body .depth current = .done depth afterDepth ∧
      callback old body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth =
        .done ordinary afterOrdinary ∧
      construct old body current = request true depth ordinary (callback old body) afterOrdinary := by
  obtain ⟨depth, afterDepth, depthDone⟩ := callback_complete old body .depth source current facts available prepared
  obtain ⟨ordinary, afterOrdinary, ordinaryDone⟩ := callback_complete old body
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) source afterDepth facts available prepared
  refine ⟨depth, afterDepth, ordinary, afterOrdinary, depthDone, ordinaryDone, ?_⟩
  simp only [construct, depthDone, Outcome.bind, ordinaryDone]

/-- A prepared constructor can report pending only at its exact post-probe key, before any fresh body call. -/
theorem pending_exact [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (source current : State Symbol Guard) (facts : Facts source) (available : Available source body)
    (prepared : InternedStoredClosedMuCompletion.PreparedWithoutMu body) :
    ∃ depth afterDepth ordinary afterOrdinary,
      callback old body .depth current = .done depth afterDepth ∧
      callback old body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth =
        .done ordinary afterOrdinary ∧
      ∀ key final, construct old body current = .pending key final ↔
        (∃ entry, afterOrdinary.nodes.table (muKey depth ordinary) = some entry) ∧
          afterOrdinary.nodeRecords (muKey depth ordinary) = none ∧
          key = muKey depth ordinary ∧ final = afterOrdinary := by
  obtain ⟨depth, afterDepth, ordinary, afterOrdinary, depthDone, ordinaryDone, expanded⟩ :=
    probes_complete old body source current facts available prepared
  refine ⟨depth, afterDepth, ordinary, afterOrdinary, depthDone, ordinaryDone, ?_⟩
  intro key final
  rw [expanded]
  cases installed : afterOrdinary.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases stored : afterOrdinary.nodeRecords (muKey depth ordinary) with
      | some value => simp [request, installed, stored]
      | none =>
          simp only [request, installed, stored]
          constructor
          · intro equal
            obtain ⟨sameKey, sameState⟩ := Outcome.pending.inj equal
            exact ⟨⟨entry, rfl⟩, True.intro, sameKey.symm, sameState.symm⟩
          · rintro ⟨_, _, rfl, rfl⟩
            rfl
  | none =>
      let entry := Cache.intern afterOrdinary.nodes (muKey depth ordinary)
      let allocated := {afterOrdinary with nodes := entry.2}
      obtain ⟨actual, afterBody, actualDone⟩ := callback_complete old body (.interned entry.1.identity)
        source allocated facts available prepared
      simp only [request, installed]
      change (callback old body (.interned entry.1.identity) allocated).bind _ = .pending key final ↔ _
      rw [actualDone]
      simp [Outcome.bind]

/-- Prepared bodies in complete caches derive finite actual first-run binder execution. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state body)
    (covered : InternedRecordCoherence.Covered [] state)
    (prepared : InternedStoredClosedMuCompletion.PreparedWithoutMu body) :
    ∃ value final, maybeMu key body state = .done value final ∧ Facts final ∧ Available final value ∧
      Grows state final ∧ Extends state.nodes.issued final.nodes.issued := by
  have checked := verified key body state facts available
  have done : ∃ value final, maybeMu key body state = .done value final := by
    rw [maybeMu_eq key body state state facts available]
    split
    · exact InternedFreshOrdinaryFirstOrderCompletion.binder_complete true _
        (InternedStoredClosedMuCompletion.encode_withoutMu _ _ body prepared) _ state facts.coherent.valid covered
    · exact ⟨body, state, rfl⟩
  obtain ⟨value, final, done⟩ := done
  exact ⟨value, final, done, by simpa only [done, Outcome.state] using checked.facts,
    checked.result value final done, by simpa only [done, Outcome.state] using checked.growth,
    by simpa only [done, Outcome.state] using checked.history⟩

/-- Every completed optional-binder call replays the exact result without allocation after later cache growth. -/
theorem replay [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (before final after : State Symbol Guard) (facts : Facts before) (available : Available before body)
    (value : Value Symbol Guard) (done : maybeMu key body before = .done value final) (growth : Grows final after) :
    maybeMu key body after = .done value after := by
  rw [maybeMu_eq key body before before facts available] at done
  rw [maybeMu_eq key body before after facts available]
  split at done
  · rename_i used
    rw [ite_eq_left used]
    exact InternedFreshOrdinaryReplay.build_replay _ _ before after value final facts.coherent.valid done growth
  · rename_i absent
    rw [ite_eq_right absent]
    obtain ⟨rfl, rfl⟩ := Outcome.done.inj done
    rfl

end MicroCFTA.SourceRecursiveIntersectionMaybeMu
