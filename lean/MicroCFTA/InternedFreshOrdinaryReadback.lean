import MicroCFTA.InternedFreshOrdinaryOrigins
import MicroCFTA.InternedFreshOrdinaryPending
import MicroCFTA.InternedProfileHeap

/-!
# Exact stored probes and fresh-body readback for the repaired executor

A completed miss stores its actual fresh body and both actual probe records.
Canonical hits recover the complete requested probes. The matcher fast paths
use the same ordinary argument selected from the stored Depth probe.
-/
namespace MicroCFTA.InternedFreshOrdinaryReadback
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish IsPending)
open InternedNestedFacts InternedNestedSpecialization
open InternedNestedProvenance (Values depth_available ordinary_available)
open InternedNestedMissReadback (missing_record)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryOrigins InternedFreshOrdinaryPending
open InternedBinderProtocol (Reference NodeKey)

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

/-- Read only the two stored-probe fast paths of a recursive payload. -/
def storedProbe (value : Value Symbol Guard) (name : Reference) : Option (Value Symbol Guard) :=
  match value with
  | .mu _ _ depth ordinary => probeReadback depth ordinary name
  | _ => none

/-- A canonical hit identifies both full requested records and the chosen matcher argument. -/
theorem hit_probes (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (present : state.nodeRecords (muKey depth ordinary) = some value) :
    ∃ entry body, value = .mu entry body depth ordinary ∧
      storedProbe value .depth = some depth ∧
      storedProbe value (.uninterned (ordinaryLevel depth)) = some ordinary ∧
      .uninterned (ordinaryLevel depth) ∉ depth.free := by
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state facts
    depthAvailable ordinaryAvailable present
  exact ⟨entry, body, rfl, probeReadback_depth depth ordinary, probeReadback_ordinary depth ordinary,
    ordinary_fresh depth⟩

/-- Every stored repaired Mu from a closed run has actual callback origins and exact matcher fast paths. -/
theorem closed_stored_probes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    Origin entry body depth ordinary ∧
      storedProbe (.mu entry body depth ordinary) .depth = some depth ∧
      storedProbe (.mu entry body depth ordinary) (.uninterned (ordinaryLevel depth)) = some ordinary ∧
      .uninterned (ordinaryLevel depth) ∉ depth.free :=
  ⟨closed_origins expression key entry body depth ordinary present,
    probeReadback_depth depth ordinary, probeReadback_ordinary depth ordinary, ordinary_fresh depth⟩

end MicroCFTA.InternedFreshOrdinaryReadback
