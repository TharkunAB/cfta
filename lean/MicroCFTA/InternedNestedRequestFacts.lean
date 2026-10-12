import MicroCFTA.InternedNestedFacts

/-!
# Complete provenance for the actual nested Mu request

The source request either reads a complete record, reports a pending key,
or reserves an identity and constructs its body. This module verifies all
three branches from local constructor facts and actual state histories.
-/
namespace MicroCFTA.InternedNestedRequestFacts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedConstructionProvenance InternedEdgeResidency
open InternedNestedConstruction InternedNestedFacts
open InternedBinderProtocol (Reference NodeKey)

/-- Finish the source miss branch after its body has returned. -/
def complete (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  let key := muKey depth ordinary
  let candidate := Value.mu entry body depth ordinary
  let records := keepFirst state.nodeRecords key candidate
  .done (finish smart ((records key).getD candidate)) {state with nodeRecords := records}

/-- Completing the reserved Mu establishes the new record from its available
body and probe values. An existing completed payload retains first-writer behavior. -/
theorem complete_verified (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (storedEntry : state.nodes.table (muKey depth ordinary) = some entry)
    (bodyAvailable : Available state body) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) :
    Verified state (complete smart entry body depth ordinary state) Available := by
  let key := muKey depth ordinary
  let candidate := Value.mu entry body depth ordinary
  let later := {state with nodeRecords := keepFirst state.nodeRecords key candidate}
  have growth : Grows state later :=
    ⟨extends_refl _, extends_refl _, extends_refl _, keepFirst_extends _ _ _⟩
  have coherent : Coherent later := by
    refine ⟨facts.coherent.valid, facts.coherent.edges, ?_⟩
    intro other value present
    rcases record_cases state.nodeRecords key other candidate value present with old | ⟨same, equal⟩
    · exact facts.coherent.nodes other value old
    · subst other value
      exact ⟨entry, storedEntry, rfl, rfl⟩
  have bodyLater := bodyAvailable.grows state later growth (extends_refl _)
  have depthLater := depthAvailable.grows state later growth (extends_refl _)
  have ordinaryLater := ordinaryAvailable.grows state later growth (extends_refl _)
  have cached : Cached later := by
    constructor
    · intro other edge present child member
      exact (facts.cached.edges other edge present child member).grows state later growth (extends_refl _)
    · intro other value present
      rcases record_cases state.nodeRecords key other candidate value present with old | ⟨same, equal⟩
      · exact (facts.cached.nodes other value old).grows state later growth (extends_refl _)
      · subst other value
        refine .intro candidate (stored_resident later coherent key candidate present)
          (identifyMu_issued later.nodes entry body depth ordinary bodyLater.issued) ?_
        intro child member
        simp only [candidate, children, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact bodyLater
        · exact depthLater
        · exact ordinaryLater
  have linked : Linked later := by
    intro other value present edge member
    rcases record_cases state.nodeRecords key other candidate value present with old | ⟨same, equal⟩
    · exact facts.linked other value old edge member
    · subst other value
      simp [candidate, nodeEdges] at member
  have present : later.nodeRecords key = some ((later.nodeRecords key).getD candidate) := by
    obtain ⟨value, found⟩ := keepFirst_present state.nodeRecords key candidate
    simp [later, found]
  refine ⟨⟨coherent, cached, linked⟩, growth, extends_refl _, ?_⟩
  intro value after same
  cases same
  exact finish_available smart _ (cached.nodes key _ present)

/-- The full source Mu request preserves record invariants even when its
actual body construction reaches an unfinished canonical record. -/
theorem request_verified [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (bodyVerified : ∀ name current, Grows state current → Extends state.nodes.issued current.nodes.issued →
      Facts current → Available current (.reference name) →
      Verified current (callback name current) Available) :
    Verified state (request smart depth ordinary callback state) Available := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases found : state.nodeRecords (muKey depth ordinary) with
      | none => simpa only [request, installed, found] using pending_verified state facts (muKey depth ordinary) Available
      | some value =>
          simpa only [request, installed, found] using pure_verified state facts (finish smart value) Available
            (finish_available smart value (facts.cached.nodes _ value found))
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have reserved := Cache.intern_correct state.nodes key facts.coherent.valid.2
      have growth : Grows state allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends state.nodes key facts.coherent.valid.2
      have built := bodyVerified (.interned entry.1.identity) allocated growth history (reserve_facts key state facts)
        (reserve_available key state facts.coherent facts.cached).2
      have called : Verified state (callback (.interned entry.1.identity) allocated) Available :=
        ⟨built.facts, grows_trans growth built.growth, extends_trans history built.history, built.result⟩
      have result := bind_verified state (callback (.interned entry.1.identity) allocated)
        (fun body after => complete smart entry.1 body depth ordinary after) Available Available called (by
          intro body after returned afterFacts bodyAvailable
          have finalEntry : after.nodes.table key = some entry.1 := by
            have retained := built.growth.nodes key entry.1 reserved.2.1
            simpa [returned, Outcome.state] using retained
          have finalDepth : Available after depth := by
            simpa [returned, Outcome.state] using called.available depth depthAvailable
          have finalOrdinary : Available after ordinary := by
            simpa [returned, Outcome.state] using called.available ordinary ordinaryAvailable
          exact complete_verified smart entry.1 body depth ordinary after afterFacts finalEntry
            bodyAvailable finalDepth finalOrdinary)
      simpa only [request, installed, complete, entry, allocated, key] using result

end MicroCFTA.InternedNestedRequestFacts
