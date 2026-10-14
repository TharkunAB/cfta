import MicroCFTA.SourceRecursiveIntersectionMaybeMuCoverage

/-!
# Exact pending phase of an actual complete-cache binder call

Complete incoming coverage excludes an incomplete final cache hit after
both successful probes. A pending constructor must instead stop inside
its Depth callback, its ordinary callback, or its fresh body callback.
Each case retains the actual source equations and intermediate caches.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMaybeMu
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedNestedConstruction (Outcome request)
open InternedBinderProtocol (Reference NodeKey)

/-- A pending canonical request in a complete cache has a genuine fresh reservation and pending body call. -/
theorem request_pending_fresh [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (call : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state final : State Symbol Guard) (key : NodeKey) (covered : Covered [] state)
    (stopped : request smart depth ordinary call state = .pending key final) :
    state.nodes.table (muKey depth ordinary) = none ∧
      call (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)
        {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} = .pending key final := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      rcases covered.nodes _ entry installed with impossible | ⟨record, stored⟩
      · cases impossible
      · simp only [request, installed, stored] at stopped; cases stopped
  | none =>
      refine ⟨rfl, ?_⟩
      let entry := Cache.intern state.nodes (muKey depth ordinary)
      let allocated := {state with nodes := entry.2}
      simp only [request, installed] at stopped
      change (call (.interned entry.1.identity) allocated).bind _ = .pending key final at stopped
      cases actual : call (.interned entry.1.identity) allocated with
      | done value after => rw [actual] at stopped; cases stopped
      | pending pending after =>
          have same := Outcome.pending.inj (by simpa only [actual, Outcome.bind] using stopped)
          simp only [same.1, same.2]

/-- A pending source binder retains the exact callback phase where the actual computation stopped. -/
inductive PendingPhase [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) (key : NodeKey) (final : State Symbol Guard) : Prop where
  | depth (stopped : callback old body .depth state = .pending key final) : PendingPhase old body state key final
  | ordinary (depth : Value Symbol Guard) (afterDepth : State Symbol Guard)
      (depthDone : callback old body .depth state = .done depth afterDepth)
      (stopped : callback old body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth = .pending key final) :
      PendingPhase old body state key final
  | fresh (depth ordinary : Value Symbol Guard) (afterDepth afterOrdinary : State Symbol Guard)
      (depthDone : callback old body .depth state = .done depth afterDepth)
      (ordinaryDone : callback old body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth = .done ordinary afterOrdinary)
      (missing : afterOrdinary.nodes.table (muKey depth ordinary) = none)
      (stopped : callback old body (.interned (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).1.identity)
        {afterOrdinary with nodes := (Cache.intern afterOrdinary.nodes (muKey depth ordinary)).2} = .pending key final) :
      PendingPhase old body state key final

/-- Actual source effects and complete incoming coverage derive the precise pending callback phase. -/
theorem construct_pending_phase [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey) (valid : Valid state) (covered : Covered [] state)
    (stopped : construct old body state = .pending key final) : PendingPhase old body state key final := by
  cases depthActual : callback old body .depth state with
  | pending pending after =>
      have same := Outcome.pending.inj (by simpa only [construct, depthActual, Outcome.bind] using stopped)
      exact .depth (by simpa only [same.1, same.2] using depthActual)
  | done depth afterDepth =>
      have depthValid : Valid afterDepth := by simpa only [depthActual, Outcome.state] using (callback_correct old body .depth state valid).1
      have depthCovered := callback_covered old body .depth state valid covered depth afterDepth depthActual
      let name := Reference.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)
      cases ordinaryActual : callback old body name afterDepth with
      | pending pending after =>
          dsimp only [name] at ordinaryActual
          have same := Outcome.pending.inj (by simpa only [construct, depthActual, Outcome.bind, ordinaryActual] using stopped)
          exact .ordinary depth afterDepth depthActual (by simpa only [same.1, same.2] using ordinaryActual)
      | done ordinary afterOrdinary =>
          dsimp only [name] at ordinaryActual
          have ordinaryCovered := callback_covered old body name afterDepth depthValid depthCovered ordinary afterOrdinary ordinaryActual
          have requestStopped : request true depth ordinary (callback old body) afterOrdinary = .pending key final := by
            simpa only [construct, depthActual, Outcome.bind, ordinaryActual] using stopped
          obtain ⟨missing, freshStopped⟩ := request_pending_fresh true depth ordinary (callback old body) afterOrdinary final key ordinaryCovered requestStopped
          exact .fresh depth ordinary afterDepth afterOrdinary depthActual ordinaryActual missing freshStopped

/-- A pending optional binder retains its actual free pair name and precise internal callback phase. -/
theorem maybeMu_pending_phase [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey) (valid : Valid state) (covered : Covered [] state)
    (stopped : maybeMu pair body state = .pending key final) :
    Reference.intersection pair.1 pair.2 ∈ body.free ∧ PendingPhase (.intersection pair.1 pair.2) body state key final := by
  unfold maybeMu at stopped
  split at stopped
  · exact ⟨by assumption, construct_pending_phase _ body state final key valid covered stopped⟩
  · cases stopped

end MicroCFTA.SourceRecursiveIntersectionMaybeMu
