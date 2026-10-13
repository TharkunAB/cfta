import MicroCFTA.InternedNestedPendingPreservation
import MicroCFTA.InternedNestedProvenance
import MicroCFTA.InternedNestedSpecialization
import MicroCFTA.InternedCleanupAge

/-!
# Exact body readback after an arbitrary source Mu cache miss

A fresh reservation remains pending throughout its actual source callback.
A successful callback therefore cannot install another payload at that key.
The final readback uses exactly the body and probes from this source call.
-/
namespace MicroCFTA.InternedNestedMissReadback
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedFacts InternedNestedProvenance InternedNestedSpecialization
open InternedBinderProtocol (Reference MuKey NodeRef)

/-- The normalized source callback retains its actual lexical environment. -/
def callback [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard) :
    Outcome Symbol Guard (Value Symbol Guard) :=
  (build body (.reference name :: environment) state).bind fun value after =>
    work (withoutSelfReference name value) after

/-- Every normalized source callback preserves a pending ancestor slot on either outcome. -/
theorem callback_pending [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (probes : MuKey NodeRef)
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (pending : IsPending (.mu probes) state) : IsPending (.mu probes) (callback body environment name state).state := by
  exact bind_preserves_pending _ _ (build_correct body _ state valid).1
    (build_preserves_pending body _ probes state valid pending)
    (fun value after afterValid afterPending => work_preserves_pending (withoutSelfReference name value)
      (withoutSelfReference_ordinary name value) probes after afterValid afterPending)

/-- Coherent record tables cannot contain a payload for a missing canonical identity. -/
theorem missing_record (state : State Symbol Guard) (coherent : Coherent state)
    (key : InternedBinderProtocol.NodeKey) (missing : state.nodes.table key = none) :
    state.nodeRecords key = none := by
  cases found : state.nodeRecords key with
  | none => rfl
  | some value =>
      obtain ⟨entry, present, _⟩ := coherent.nodes key value found
      rw [missing] at present
      cases present

/-- A successful arbitrary source miss returns its exact fresh body and original normalized probes. -/
theorem request_miss [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (missing : state.nodes.table (muKey depth ordinary) = none)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : request smart depth ordinary (callback body environment) state = .done value final) :
    let entry := Cache.intern state.nodes (muKey depth ordinary)
    let allocated := {state with nodes := entry.2}
    ∃ actual afterBody,
      callback body environment (.interned entry.1.identity) allocated = .done actual afterBody ∧
      afterBody.nodeRecords (muKey depth ordinary) = none ∧
      value = finish smart (.mu entry.1 actual depth ordinary) ∧
      final = {afterBody with nodeRecords := keepFirst afterBody.nodeRecords (muKey depth ordinary) (.mu entry.1 actual depth ordinary)} := by
  let key := muKey depth ordinary
  let entry := Cache.intern state.nodes key
  let allocated := {state with nodes := entry.2}
  have valid : InternedConstructorTemplates.Valid allocated :=
    ⟨coherent.valid.1, (Cache.intern_correct state.nodes key coherent.valid.2).1⟩
  have pending : IsPending key allocated :=
    ⟨⟨entry.1, (Cache.intern_correct state.nodes key coherent.valid.2).2.1⟩,
      missing_record state coherent key missing⟩
  have preserved := callback_pending body environment (.interned entry.1.identity)
    ⟨depth.referenceOf, ordinary.referenceOf⟩ allocated valid pending
  simp only [request, missing] at completed
  change (callback body environment (.interned entry.1.identity) allocated).bind _ = .done value final at completed
  obtain ⟨actual, afterBody, bodyDone, readback⟩ := bind_done _ _ _ _ completed
  have stillMissing : afterBody.nodeRecords key = none := by
    simpa only [bodyDone, Outcome.state, key, muKey] using preserved.2
  have candidate : keepFirst afterBody.nodeRecords key (.mu entry.1 actual depth ordinary) key =
      some (.mu entry.1 actual depth ordinary) := by simp [keepFirst, stillMissing, put]
  change Outcome.done (finish smart ((keepFirst afterBody.nodeRecords key (.mu entry.1 actual depth ordinary) key).getD _))
    {afterBody with nodeRecords := keepFirst afterBody.nodeRecords key (.mu entry.1 actual depth ordinary)} = .done value final at readback
  rw [candidate] at readback
  simp only [Option.getD_some, Outcome.done.injEq] at readback
  exact ⟨actual, afterBody, bodyDone, stillMissing, readback.1.symm, readback.2.symm⟩

/-- The exact source candidate is resident at the request key after every completed miss. -/
theorem request_miss_record [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (missing : state.nodes.table (muKey depth ordinary) = none)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : request smart depth ordinary (callback body environment) state = .done value final) :
    ∃ actual afterBody,
      callback body environment (.interned (Cache.intern state.nodes (muKey depth ordinary)).1.identity)
        {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} = .done actual afterBody ∧
      final.nodeRecords (muKey depth ordinary) = some (.mu (Cache.intern state.nodes (muKey depth ordinary)).1 actual depth ordinary) ∧
      value = finish smart (.mu (Cache.intern state.nodes (muKey depth ordinary)).1 actual depth ordinary) := by
  obtain ⟨actual, afterBody, bodyDone, absent, same, finalSame⟩ :=
    request_miss smart body environment depth ordinary state coherent missing value final completed
  refine ⟨actual, afterBody, bodyDone, ?_, same⟩
  rw [finalSame]
  simp [keepFirst, absent, put]

/-- A newly reserved source call can return a completely old value only through the two actual smart cleanup branches. -/
theorem request_miss_old [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (missing : state.nodes.table (muKey depth ordinary) = none)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : request smart depth ordinary (callback body environment) state = .done value final)
    (cutoff : Nat) (fresh : cutoff ≤ state.nodes.next)
    (old : ∀ identity, InternedNodeIdentityFootprint.Occurs identity value → identity < cutoff) :
    let entry := (Cache.intern state.nodes (muKey depth ordinary)).1
    ∃ actual afterBody,
      callback body environment (.interned entry.identity)
        {state with nodes := (Cache.intern state.nodes (muKey depth ordinary)).2} = .done actual afterBody ∧
      smart = true ∧
      ((value = actual ∧ .interned entry.identity ∉ actual.free ∧
          ∀ identity, InternedNodeIdentityFootprint.Occurs identity actual → identity < cutoff) ∨
        (value = .empty ∧ actual = .reference (.interned entry.identity))) := by
  obtain ⟨actual, afterBody, bodyDone, _, same, _⟩ :=
    request_miss smart body environment depth ordinary state coherent missing value final completed
  have freshEntry : cutoff ≤ (Cache.intern state.nodes (muKey depth ordinary)).1.identity := by
    rw [InternedFreshProbeKeys.intern_miss_identity state.nodes _ missing]
    exact fresh
  have oldFinished : ∀ identity, InternedNodeIdentityFootprint.Occurs identity
      (finish smart (.mu (Cache.intern state.nodes (muKey depth ordinary)).1 actual depth ordinary)) → identity < cutoff := by
    simpa only [← same] using old
  obtain ⟨smartTrue, cases⟩ := InternedCleanupAge.finish_old_cases smart
    (Cache.intern state.nodes (muKey depth ordinary)).1 actual depth ordinary cutoff freshEntry oldFinished
  refine ⟨actual, afterBody, bodyDone, smartTrue, ?_⟩
  rcases cases with ⟨unusedReturn, unused⟩ | ⟨emptyReturn, bare⟩
  · have equal := same.trans unusedReturn
    exact Or.inl ⟨equal, unused, fun identity occurrence => old identity (equal.symm ▸ occurrence)⟩
  · exact Or.inr ⟨same.trans emptyReturn, bare⟩

end MicroCFTA.InternedNestedMissReadback
