import MicroCFTA.SourceRecursiveIntersectionDomainAllocation
import MicroCFTA.SourceRecursiveIntersectionDomainInventory

namespace MicroCFTA.DomainAllocationKernels

open Cache IntersectionFlatMemoKeyDomain IntersectionEmptyDomain

private def repeatIntern [DecidableEq Key] (key : Key) : Nat → State Key → State Key
  | 0, state => state
  | count + 1, state => repeatIntern key count (intern state key).2

private theorem repeat_trace [DecidableEq Key] (state : State Key) (key : Key) (count : Nat) :
    CacheFiniteInterning.Trace [key] state (repeatIntern key count state) := by
  induction count generalizing state with
  | zero => exact .refl _
  | succ count ih =>
    exact (CacheFiniteInterning.Trace.intern (.refl state) key (by simp)).trans (ih _)

private theorem repeat_hit [DecidableEq Key] (state : State Key) (key : Key) (count : Nat)
    (present : state.table key = some value) : repeatIntern key count state = state := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [repeatIntern, CacheFiniteInterning.intern_hit present] using ih

/-- Arbitrarily many actual calls spend at most one identity and retain the first full state. -/
theorem repeated_single_key [DecidableEq Key] (state : State Key) (key : Key) (count : Nat) :
    CacheFiniteInterning.Trace [key] state (repeatIntern key (count + 1) state) ∧
      repeatIntern key (count + 1) state = (intern state key).2 ∧
      (repeatIntern key (count + 1) state).next ≤ state.next + 1 := by
  have trace := repeat_trace state key (count + 1)
  obtain ⟨value, present⟩ := CacheFiniteInterning.intern_present state key
  exact ⟨trace, repeat_hit _ _ count present, by simpa using trace.next_le⟩

private def nonemptyKey : DomainKey := ⟨[], [(0, 0)]⟩

private def warm : State DomainKey :=
  ⟨18, fun ident => if ident = 17 then some nonemptyKey else none,
    fun key => if key = nonemptyKey then some ⟨17, nonemptyKey⟩ else none⟩

/-- A warm raw identity seventeen returns shifted identity eighteen and retains the entire cache. -/
theorem warm_nonzero_and_empty :
    make warm nonemptyKey = (⟨18, nonemptyKey⟩, warm) ∧
      make (make warm nonemptyKey).2 emptyKey = (emptyDomain, warm) ∧
      make (make (make warm nonemptyKey).2 emptyKey).2 nonemptyKey =
        (⟨18, nonemptyKey⟩, warm) := by
  have nonempty : nonemptyKey ≠ emptyKey := by decide
  simp [make, nonempty, warm, Cache.intern]

/-- Empty requests use no inventory credit, even in a cache with a nonzero supply. -/
theorem empty_without_inventory (state : State DomainKey) :
    SourceRecursiveIntersectionDomainAllocation.Trace [] state (make state emptyKey).2 ∧
      (make state emptyKey).2 = state ∧ (make state emptyKey).1.identity = 0 := by
  exact ⟨.empty (.refl state), by simp [make_empty], by simp [make_empty, emptyDomain]⟩

/-- Two cold requests for the same domain allocate once and use the canonical inventory bound. -/
theorem cold_repeat_inventory (binders pairs)
    (member : nonemptyKey ∈ SourceRecursiveIntersectionDomainInventory.inventory binders pairs)
    {bits : Nat}
    (room : 2 ^ (binders.length + pairs.length) < 2 ^ (bits + 1)) :
    let before := Cache.emptyState (Key := DomainKey)
    let first := make before nonemptyKey
    let repeated := make (make first.2 emptyKey).2 nonemptyKey
    SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionDomainInventory.inventory binders pairs) before repeated.2 ∧
      repeated = first ∧ repeated.2.next ≤ 2 ^ (binders.length + pairs.length) ∧
      repeated.1.identity < 2 ^ (bits + 1) := by
  dsimp only
  let before := Cache.emptyState (Key := DomainKey)
  let inventory := SourceRecursiveIntersectionDomainInventory.inventory binders pairs
  have firstTrace : SourceRecursiveIntersectionDomainAllocation.Trace inventory before
      (make before nonemptyKey).2 := .step (.refl before) nonemptyKey member
  have trace := (firstTrace.empty).step nonemptyKey member
  have nonempty : nonemptyKey ≠ emptyKey := by decide
  have repeatedSame : make (make (make before nonemptyKey).2 emptyKey).2 nonemptyKey =
      make before nonemptyKey := by
    obtain ⟨_valid, present, _key⟩ := Cache.intern_correct before nonemptyKey Cache.empty_valid
    simp [make, nonempty, CacheFiniteInterning.intern_hit present]
  have represented := (IntersectionEmptyDomain.make_correct before Cache.empty_valid nonemptyKey).2
  have firstRoom : before.next + inventory.length < 2 ^ (bits + 1) := by
    simpa [before, inventory, Cache.emptyState,
      SourceRecursiveIntersectionDomainInventory.inventory_length] using room
  have bounded := trace.next_le
  have identity := firstTrace.identity_lt Cache.empty_valid represented firstRoom
  refine ⟨trace, repeatedSame, ?_, ?_⟩
  · simpa [before, inventory, Cache.emptyState,
      SourceRecursiveIntersectionDomainInventory.inventory_length] using bounded
  · simpa [repeatedSame] using identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms repeated_single_key
#check @repeated_single_key
#print axioms warm_nonzero_and_empty
#check @warm_nonzero_and_empty
#print axioms empty_without_inventory
#check @empty_without_inventory
#print axioms cold_repeat_inventory
#check @cold_repeat_inventory

end MicroCFTA.DomainAllocationKernels
