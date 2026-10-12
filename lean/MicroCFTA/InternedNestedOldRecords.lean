import MicroCFTA.InternedNestedPendingPreservation
import MicroCFTA.InternedNestedDenseIdentities
import MicroCFTA.InternedNodeIdentityFootprint

/-!
# Old canonical records already exist before nested construction

A dense source table already contains every earlier canonical identity.
An unfinished old Mu payload cannot complete inside another source call.
Therefore a resident old identity at return or pending readback has the
same complete payload before the call. This applies to arbitrary syntax.
-/
namespace MicroCFTA.Cache

/-- Canonical identity growth cannot introduce a new entry below the earlier dense counter. -/
theorem old_entry (before after : State Key) (dense : Dense before) (valid : Valid after)
    (growth : Extends before.table after.table) (entry : Interned Key)
    (present : after.table entry.key = some entry) (earlier : entry.identity < before.next) :
    before.table entry.key = some entry := by
  obtain ⟨key, stored⟩ := dense entry.identity earlier
  have same := (identity_eq_iff_key_eq after valid (growth key _ stored) present).mp rfl
  subst key
  exact stored

end MicroCFTA.Cache

namespace MicroCFTA.InternedNestedOldRecords
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedPendingOrigins InternedNodeIdentityFootprint
open InternedBinderProtocol (NodeKey)

/-- Every allowed pending key with an actual reservation origin is a Mu key. -/
theorem origin_mu {key : NodeKey} {state : State Symbol Guard} (origin : Origin key state) :
    ∃ probes, key = .mu probes := by
  obtain ⟨before, depth, ordinary, same, rest⟩ := origin
  exact ⟨_, same⟩

/-- An old resident node payload cannot first appear during arbitrary nested source execution. -/
theorem build_old_record [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (inputs : Values before environment) (dense : Cache.Dense before.nodes)
    (origins : Origins pending before) (covered : Covered pending before)
    (value : Value Symbol Guard) (entry : Interned NodeKey)
    (resident : Resident (build expression environment before).state value)
    (field : entryOf value = some entry) (earlier : entry.identity < before.nodes.next) :
    before.nodeRecords entry.key = some value := by
  let after := (build expression environment before).state
  have verified := build_verified expression environment before facts inputs
  have finalEntry := resident_entry after verified.facts.coherent value resident entry field
  have oldEntry := Cache.old_entry before.nodes after.nodes dense verified.facts.coherent.valid.2
    verified.growth.nodes entry finalEntry earlier
  cases oldRecord : before.nodeRecords entry.key with
  | some old =>
      have same := Option.some.inj ((verified.growth.nodeRecords entry.key old oldRecord).symm.trans (resident entry field))
      exact congrArg some same
  | none =>
      have allowed : entry.key ∈ pending := by
        rcases covered.nodes entry.key entry oldEntry with member | ⟨old, impossible⟩
        · exact member
        · rw [oldRecord] at impossible
          cases impossible
      obtain ⟨probes, same⟩ := origin_mu (origins entry.key allowed)
      have initialPending : IsPending (.mu probes) before := by
        rw [← same]
        exact ⟨⟨entry, oldEntry⟩, oldRecord⟩
      have finalMissing := (build_preserves_pending expression environment probes before facts.coherent.valid initialPending).2
      rw [← same, resident entry field] at finalMissing
      cases finalMissing

/-- A resident record whose complete identity footprint predates the call is already fully available before it. -/
theorem build_old_available [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (inputs : Values before environment) (dense : Cache.Dense before.nodes)
    (origins : Origins pending before) (covered : Covered pending before)
    (value : Value Symbol Guard) (resident : Resident (build expression environment before).state value)
    (earlier : ∀ identity, Occurs identity value → identity < before.nodes.next) : Available before value := by
  cases value with
  | empty => exact empty_available before
  | reference name =>
      apply reference_available before name
      intro identity member
      have same : name = .interned identity := (List.mem_singleton.mp member).symm
      subst name
      obtain ⟨key, present⟩ := dense identity (earlier identity .reference)
      exact ⟨key, (facts.coherent.valid.2.2 key _ present).2⟩
  | node entry edges depth free =>
      exact facts.cached.nodes entry.key _ (build_old_record expression environment before facts inputs dense origins covered
        _ entry resident rfl (earlier entry.identity (.entry _ entry rfl rfl)))
  | union entry members depth free =>
      exact facts.cached.nodes entry.key _ (build_old_record expression environment before facts inputs dense origins covered
        _ entry resident rfl (earlier entry.identity (.entry _ entry rfl rfl)))
  | mu entry body depth ordinary =>
      exact facts.cached.nodes entry.key _ (build_old_record expression environment before facts inputs dense origins covered
        _ entry resident rfl (earlier entry.identity (.entry _ entry rfl rfl)))

/-- After any actual completed empty-cache run, a later call cannot create an older canonical payload. -/
theorem completed_prefix_old_record [DecidableEq (EdgeKey Symbol Guard)]
    (first expression : Syntax Symbol Guard) (firstValue : Value Symbol Guard) (before : State Symbol Guard)
    (completed : build first [] empty = .done firstValue before)
    (environment : List (Value Symbol Guard)) (inputs : Values before environment)
    (value : Value Symbol Guard) (entry : Interned NodeKey)
    (resident : Resident (build expression environment before).state value)
    (field : entryOf value = some entry) (earlier : entry.identity < before.nodes.next) :
    before.nodeRecords entry.key = some value := by
  have facts : Facts before := by simpa only [completed, Outcome.state] using (closed_verified first).facts
  have dense : InternedNestedDenseIdentities.Dense before := by
    simpa only [completed, Outcome.state] using InternedNestedDenseIdentities.closed_dense first
  have covered : Covered [] before := InternedNestedCoverage.closed_covered first firstValue before completed
  exact build_old_record expression environment before facts inputs dense.2
    (fun _ impossible => by cases impossible) covered value entry resident field earlier

end MicroCFTA.InternedNestedOldRecords
