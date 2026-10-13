import MicroCFTA.InternedBinderFreeDepthBound
import MicroCFTA.InternedFreshOrdinaryReadback

/-!
# Prepared source heaps from repaired first-order construction

With depth-zero captured inputs, every actual body callback has depth zero.
Ordinary work preserves earlier Mu records. Completing the current reservation
adds only its depth-zero body. The resulting cache satisfies the existing
finite Mu/union exposure precondition without an assumed stored-knot witness.
-/
namespace MicroCFTA.InternedFreshOrdinaryFirstOrderHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work request)
open InternedNestedFacts InternedNestedRequestFacts InternedNestedProvenance
open InternedFreshProbeKeys InternedShallowHeap
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedStoredShallowCompletion
open InternedBinderProtocol (Reference NodeKey)

/-- A binder-free repaired callback introduces no complete Mu payload. -/
theorem callback_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (free : BinderFree body) (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) :
    NoNewMu state (callback body environment name state).state := by
  unfold callback
  rw [InternedFreshOrdinaryStoredSubstitution.build_eq body _ state free]
  exact bind_noNewMu state _ _ (build_noNewMu body _ state free)
    (fun value after _ => InternedStoredMuOrigins.filter_noNewMu name value after)

/-- First-writer completion preserves old depth-zero bodies and adds the actual new body. -/
theorem complete_shallow (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (shallow : Shallow state) (zero : body.depth = 0) :
    Shallow {state with nodeRecords := keepFirst state.nodeRecords (muKey depth ordinary) (.mu entry body depth ordinary)} := by
  intro key actual actualBody actualDepth actualOrdinary stored
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
      (.mu actual actualBody actualDepth actualOrdinary) stored with old | ⟨_, same⟩
  · exact shallow key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact zero

/-- The repaired source binder derives the complete depth-zero stored-body invariant. -/
theorem binder_shallow [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (free : BinderFree body) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (shallow : Shallow state)
    (depths : ∀ value ∈ environment, value.depth = 0) :
    Shallow (build (.binder smart body) environment state).state := by
  have invoke : ∀ name current, Facts current → Values current environment → Shallow current →
      Available current (.reference name) →
      ∃ value after, callback body environment name current = .done value after ∧
        Facts after ∧ Values after environment ∧ Shallow after ∧ value.depth = 0 := by
    intro name current currentFacts currentInputs currentShallow localAvailable
    have localInputs : Values current (.reference name :: environment) := by
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact localAvailable
      · exact currentInputs value member
    obtain ⟨value, after, done⟩ :=
      InternedFreshOrdinaryFirstOrderCompletion.callback_complete body free environment name current
    have checked := callback_verified body environment name current currentFacts localInputs
    have afterFacts : Facts after := by simpa only [done, Outcome.state] using checked.facts
    have afterInputs : Values after environment := fun item member => by
      simpa only [done, Outcome.state] using checked.available item (currentInputs item member)
    have afterShallow : Shallow after := by
      have retained := shallow_preserved current _ currentShallow (callback_noNewMu body free environment name current)
      simpa only [done, Outcome.state] using retained
    have zero : value.depth = 0 := Nat.eq_zero_of_le_zero
      (InternedBinderFreeDepthBound.callback_bound body free environment name current currentFacts localInputs 0
        (fun item member => Nat.le_of_eq (depths item member)) value after done)
    exact ⟨value, after, done, afterFacts, afterInputs, afterShallow, zero⟩
  obtain ⟨depth, afterDepth, depthDone, depthFacts, depthInputs, depthShallow, _⟩ :=
    invoke .depth state facts inputs shallow (depth_available state)
  obtain ⟨ordinary, afterOrdinary, ordinaryDone, ordinaryFacts, ordinaryInputs, ordinaryShallow, _⟩ :=
    invoke (.uninterned (ordinaryLevel depth)) afterDepth depthFacts depthInputs depthShallow
      (ordinary_available afterDepth (ordinaryLevel depth))
  have expanded : build (.binder smart body) environment state =
      request smart depth ordinary (callback body environment) afterOrdinary := by
    rw [build]
    change (callback body environment .depth state).bind _ = _
    rw [depthDone]
    change (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind _ = _
    rw [ordinaryDone]
    rfl
  rw [expanded]
  cases installed : afterOrdinary.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases stored : afterOrdinary.nodeRecords (muKey depth ordinary) <;>
        simpa only [request, installed, stored, Outcome.state] using ordinaryShallow
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern afterOrdinary.nodes key
      let allocated := {afterOrdinary with nodes := entry.2}
      have allocatedFacts : Facts allocated := reserve_facts key afterOrdinary ordinaryFacts
      have reserved : Available allocated (.reference (.interned entry.1.identity)) :=
        (InternedConstructionProvenance.reserve_available key afterOrdinary ordinaryFacts.coherent ordinaryFacts.cached).2
      have growth : Grows afterOrdinary allocated :=
        ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
      have history := intern_issued_extends afterOrdinary.nodes key ordinaryFacts.coherent.valid.2
      have allocatedInputs : Values allocated environment := fun value member =>
        (ordinaryInputs value member).grows afterOrdinary allocated growth history
      have allocatedShallow : Shallow allocated := ordinaryShallow
      obtain ⟨actual, afterBody, actualDone, _, _, afterShallow, zero⟩ :=
        invoke (.interned entry.1.identity) allocated allocatedFacts allocatedInputs allocatedShallow reserved
      simp only [request, installed]
      change Shallow ((callback body environment (.interned entry.1.identity) allocated).bind _).state
      rw [actualDone]
      simpa only [Outcome.bind, Outcome.state] using complete_shallow entry.1 actual depth ordinary afterBody afterShallow zero

/-- Empty-cache construction supplies all stored-body preparation premises for finite exposure. -/
theorem closed_prepared [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (free : BinderFree body) :
    ∃ value final, build (.binder smart body) [] empty = .done value final ∧
      Facts final ∧ Available final value ∧ MergedPhysicalWarmup.Prepared final := by
  obtain ⟨value, final, done, facts, available, _, _⟩ :=
    InternedFreshOrdinaryFirstOrderCompletion.closed_verified_complete smart body free
  have shallow : Shallow final := by
    have derived := binder_shallow smart body free [] empty empty_facts (by simp [Values]) empty_shallow (by simp)
    simpa only [done, Outcome.state] using derived
  exact ⟨value, final, done, facts, available, MergedPhysicalWarmup.prepared_of_shallow final facts shallow⟩

end MicroCFTA.InternedFreshOrdinaryFirstOrderHeap
