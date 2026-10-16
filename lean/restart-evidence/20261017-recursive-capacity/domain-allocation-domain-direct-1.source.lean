import MicroCFTA.CacheFiniteInterning
import MicroCFTA.IntersectionEmptyDomain

/-!
# Finite sequential domain allocation

The trace records actual calls to the reserved-zero domain constructor.
Empty domains retain the entire cache. Nonempty domains use sequential interning.
The static inventory bounds new identities independently of the trace length.
-/

namespace MicroCFTA.SourceRecursiveIntersectionDomainAllocation

open Cache IntersectionFlatMemoKeyDomain IntersectionEmptyDomain

/-- Empty calls need no inventory entry. Every other call uses an inventory key. -/
inductive Trace (inventory : List DomainKey) : Cache.State DomainKey → Cache.State DomainKey → Prop where
  | refl (state : Cache.State DomainKey) : Trace inventory state state
  | make (earlier : Trace inventory before middle) (key : DomainKey)
      (member : key = emptyKey ∨ key ∈ inventory) :
      Trace inventory before (IntersectionEmptyDomain.make middle key).2

variable {inventory : List DomainKey} {before middle after : Cache.State DomainKey}

/-- An empty call preserves the exact current state. -/
theorem Trace.empty (earlier : Trace inventory before middle) :
    Trace inventory before (IntersectionEmptyDomain.make middle emptyKey).2 :=
  .make earlier emptyKey (Or.inl rfl)

/-- Every inventory member can be passed to the actual domain constructor. -/
theorem Trace.step (earlier : Trace inventory before middle) (key : DomainKey)
    (member : key ∈ inventory) :
    Trace inventory before (IntersectionEmptyDomain.make middle key).2 :=
  .make earlier key (Or.inr member)

/-- Domain traces contain only actual intern calls and unchanged empty calls. -/
theorem Trace.interns (trace : Trace inventory before after) :
    CacheFiniteInterning.Trace inventory before after := by
  induction trace with
  | refl => exact .refl _
  | make _ key member ih =>
    by_cases empty : key = emptyKey
    · simpa [IntersectionEmptyDomain.make, empty] using ih
    · have present := member.resolve_left empty
      simpa [IntersectionEmptyDomain.make, empty] using
        CacheFiniteInterning.Trace.intern ih key present

/-- Two actual histories can be joined at the same cache. -/
theorem Trace.trans (first : Trace inventory before middle)
    (last : Trace inventory middle after) : Trace inventory before after := by
  induction last with
  | refl => exact first
  | make _ key member ih => exact .make ih key member

/-- The actual domain history preserves cache validity. -/
theorem Trace.valid (trace : Trace inventory before after) (valid : Cache.Valid before) :
    Cache.Valid after := trace.interns.valid valid

/-- The history retains every earlier canonical table entry. -/
theorem Trace.extends (trace : Trace inventory before after) :
    Cache.Extends before.table after.table := trace.interns.extends

/-- A miss spends an initial missing-key credit. -/
theorem Trace.potential (trace : Trace inventory before after) :
    after.next + CacheFiniteInterning.missing inventory after ≤
      before.next + CacheFiniteInterning.missing inventory before := trace.interns.potential

/-- Initially present keys do not require new identities. -/
theorem Trace.next_le_missing (trace : Trace inventory before after) :
    after.next ≤ before.next + CacheFiniteInterning.missing inventory before :=
  trace.interns.next_le_missing

/-- The static inventory bounds the supply after any number of calls. -/
theorem Trace.next_le (trace : Trace inventory before after) :
    after.next ≤ before.next + inventory.length := trace.interns.next_le

/-- A shifted domain remains represented after table growth. -/
theorem represents_mono {key : DomainKey} {domain : Interned DomainKey}
    (growth : Cache.Extends before.table after.table)
    (represented : Represents before key domain) : Represents after key domain := by
  refine ⟨represented.1, ?_⟩
  by_cases empty : key = emptyKey
  · simpa [empty] using represented.2
  · obtain ⟨raw, present, identity⟩ := by simpa [empty] using represented.2
    exact by simpa [empty] using And.intro (growth key raw present) identity |>.exists

/-- The shifted identity is at most the raw supply. The reserved empty identity is zero. -/
theorem represented_identity_le {state : Cache.State DomainKey} {key : DomainKey}
    {domain : Interned DomainKey} (valid : Cache.Valid state)
    (represented : Represents state key domain) : domain.identity ≤ state.next := by
  by_cases empty : key = emptyKey
  · have zero : domain.identity = 0 := by simpa [empty] using represented.2
    omega
  · obtain ⟨raw, present, identity⟩ := by simpa [empty] using represented.2
    have issued := (valid.2 key raw present).2
    have reserved := valid.1 raw.identity key issued
    omega

/-- Every represented domain uses an identity within the initial inventory budget. -/
theorem Trace.identity_le (trace : Trace inventory before after) (valid : Cache.Valid before)
    {key : DomainKey} {domain : Interned DomainKey} (represented : Represents after key domain) :
    domain.identity ≤ before.next + inventory.length := by
  exact Nat.le_trans (represented_identity_le (trace.valid valid) represented) trace.next_le

/-- Strict headroom for the inventory also bounds the shifted returned identity. -/
theorem Trace.identity_lt (trace : Trace inventory before after) (valid : Cache.Valid before)
    {key : DomainKey} {domain : Interned DomainKey} (represented : Represents after key domain)
    {limit : Nat} (room : before.next + inventory.length < limit) : domain.identity < limit :=
  Nat.lt_of_le_of_lt (trace.identity_le valid represented) room

/-- A literal return remains represented after every later actual domain call. -/
theorem Trace.returned (trace : Trace inventory (IntersectionEmptyDomain.make before key).2 after)
    (valid : Cache.Valid before) :
    Represents after key (IntersectionEmptyDomain.make before key).1 := by
  exact represents_mono trace.extends (IntersectionEmptyDomain.make_correct before valid key).2

end MicroCFTA.SourceRecursiveIntersectionDomainAllocation
