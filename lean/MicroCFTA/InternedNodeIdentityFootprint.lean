import MicroCFTA.InternedPendingProbeAbsence

/-!
# All stored node identities precede a possible pending reservation

Available records contain only issued node identities and recursive names.
The relation visits ordinary children, union members, and all three stored
Mu records, including both probes. It also includes bound names that a
cached free-name list removes. Edge identities belong to a separate cache.
-/
namespace MicroCFTA.InternedNodeIdentityFootprint
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedPendingOrigins
open InternedBinderProtocol (NodeKey)

/-- A node identity occurs as a recursive reference, a record entry, or in any complete stored child record. -/
inductive Occurs (identity : Nat) : Value Symbol Guard → Prop where
  | reference : Occurs identity (.reference (.interned identity))
  | entry (value : Value Symbol Guard) (record : Interned NodeKey)
      (present : entryOf value = some record) (same : record.identity = identity) : Occurs identity value
  | child (value child : Value Symbol Guard) (member : child ∈ children value)
      (inside : Occurs identity child) : Occurs identity value

/-- Every identity in a complete available record comes from the actual node reservation history. -/
theorem available_issued (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) :
    ∀ identity, Occurs identity value → ∃ key, state.nodes.issued identity = some key := by
  induction available with
  | intro value resident issued childAvailable ih =>
      intro identity occurrence
      cases occurrence with
      | reference => exact issued identity (by simp [Value.free])
      | entry _ record present same =>
          subst identity
          have stored := resident_entry state coherent value resident record present
          exact ⟨record.key, (coherent.valid.2.2 record.key record stored).2⟩
      | child _ child member inside => exact ih child member identity inside

/-- Every node identity and bound reference in an available record lies below the current fresh supply. -/
theorem available_below (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value)
    (identity : Nat) (occurrence : Occurs identity value) : identity < state.nodes.next := by
  obtain ⟨key, issued⟩ := available_issued state coherent value available identity occurrence
  exact coherent.valid.2.1 identity key issued

/-- Every resident pair with a pending key has only pre-reservation node identities throughout its stored records. -/
theorem origin_footprint {key : NodeKey} {state : State Symbol Guard}
    (origin : Origin key state) (coherent : Coherent state) :
    ∃ before, Grows before state ∧ before.nodes.table key = none ∧
      state.nodes.issued before.nodes.next = some key ∧
      ∀ depth ordinary, Resident state depth → Resident state ordinary → muKey depth ordinary = key →
        ∀ identity, before.nodes.next ≤ identity → ¬ Occurs identity depth ∧ ¬ Occurs identity ordinary := by
  obtain ⟨before, oldDepth, oldOrdinary, keyEq, missing, earlierCoherent, depthAvailable, ordinaryAvailable, growth, installed⟩ := origin
  let entry := (Cache.intern before.nodes key).1
  have fresh : entry.identity = before.nodes.next := intern_miss_identity before.nodes key missing
  have issued : state.nodes.issued before.nodes.next = some key := by
    rw [← fresh]
    exact (coherent.valid.2.2 key entry installed).2
  have depthResident := resident_grows before state growth oldDepth depthAvailable.resident
  have ordinaryResident := resident_grows before state growth oldOrdinary ordinaryAvailable.resident
  refine ⟨before, growth, missing, issued, ?_⟩
  intro depth ordinary newDepthResident newOrdinaryResident same identity bound
  have references : depth.referenceOf = oldDepth.referenceOf ∧ ordinary.referenceOf = oldOrdinary.referenceOf := by
    simpa only [muKey, NodeKey.mu.injEq, InternedBinderProtocol.MuKey.mk.injEq] using same.trans keyEq
  have depthEq := resident_reference_injective state coherent depth oldDepth newDepthResident depthResident references.1
  have ordinaryEq := resident_reference_injective state coherent ordinary oldOrdinary newOrdinaryResident ordinaryResident references.2
  constructor
  · intro occurrence
    have earlier := available_below before earlierCoherent oldDepth depthAvailable identity (depthEq ▸ occurrence)
    omega
  · intro occurrence
    have earlier := available_below before earlierCoherent oldOrdinary ordinaryAvailable identity (ordinaryEq ▸ occurrence)
    omega

/-- Arbitrary closed source syntax can alias a pending key only with probes that contain no later node identity or bound reference. -/
theorem closed_pending_old_footprint [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (state : State Symbol Guard) (pending : build expression [] empty = .pending key state) :
    ∃ before, Grows before state ∧ before.nodes.table key = none ∧
      state.nodes.issued before.nodes.next = some key ∧
      ∀ depth ordinary, Resident state depth → Resident state ordinary → muKey depth ordinary = key →
        ∀ identity, before.nodes.next ≤ identity → ¬ Occurs identity depth ∧ ¬ Occurs identity ordinary := by
  have facts : Facts state := by simpa only [pending, Outcome.state] using (closed_verified expression).facts
  exact origin_footprint (closed_pending_origin expression key state pending) facts.coherent

end MicroCFTA.InternedNodeIdentityFootprint
