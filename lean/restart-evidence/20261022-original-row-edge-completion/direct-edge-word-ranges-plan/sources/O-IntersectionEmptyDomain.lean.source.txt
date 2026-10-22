import MicroCFTA.IntersectionFlatMemoKeyDomain

/-!
# The reserved empty intersection domain

The current source returns identity zero without accessing the cache when
both domain containers are empty. A nonempty domain uses its raw cache
identity plus one. The machine bound therefore applies to that successor.
The prior canonical-domain and tagged-operand proofs remain unchanged.
-/

namespace MicroCFTA.IntersectionEmptyDomain

open Cache IntersectSchedule IntersectionFlatMemoKeyDomain IntersectionFlatMemoKey

/-- The structural key of the source constant emptyIntersectionDom. -/
def emptyKey : DomainKey := ⟨[], []⟩

/-- The constant empty domain needs no raw cache identity. -/
def emptyDomain : Interned DomainKey := ⟨0, emptyKey⟩

/-- The two source null checks are equivalent to the empty structural key. -/
theorem empty_iff (key : DomainKey) :
    key = emptyKey ↔ key.free = [] ∧ key.seen = [] := by
  cases key
  simp [emptyKey, DomainKey.mk.injEq]

/-- The source wrapper reserves zero and shifts every raw nonempty identity. -/
def make (state : Cache.State DomainKey) (key : DomainKey) :
    Interned DomainKey × Cache.State DomainKey :=
  if key = emptyKey then (emptyDomain, state) else
    let result := Cache.intern state key
    (⟨result.1.identity + 1, key⟩, result.2)

/-- A domain has the source identity for its structural key in the current cache. -/
def Represents (state : Cache.State DomainKey) (key : DomainKey)
    (domain : Interned DomainKey) : Prop :=
  domain.key = key ∧
    if key = emptyKey then domain.identity = 0 else
      ∃ raw, state.table key = some raw ∧ domain.identity = raw.identity + 1

/-- Creating the empty domain leaves the entire cache unchanged. -/
theorem make_empty (state : Cache.State DomainKey) :
    make state emptyKey = (emptyDomain, state) := by simp [make]

/-- The source domain constructor preserves the cache and records the shifted identity. -/
theorem make_correct (state : Cache.State DomainKey) (valid : Cache.Valid state) (key : DomainKey) :
    Cache.Valid (make state key).2 ∧ Represents (make state key).2 key (make state key).1 := by
  by_cases empty : key = emptyKey
  · subst key
    simp [make, Represents, emptyDomain, valid]
  · obtain ⟨afterValid, stored, _⟩ := Cache.intern_correct state key valid
    simp only [make, empty, ↓reduceIte, Represents]
    exact ⟨afterValid, trivial, ⟨_, stored, rfl⟩⟩

/-- Zero identifies exactly the empty structural domain. -/
theorem zero_iff (state : Cache.State DomainKey) (key : DomainKey) (domain : Interned DomainKey)
    (represented : Represents state key domain) : domain.identity = 0 ↔ key = emptyKey := by
  rcases represented with ⟨_, represented⟩
  by_cases empty : key = emptyKey
  · simpa [empty] using represented
  · simp only [empty, ↓reduceIte] at represented
    obtain ⟨raw, _, successor⟩ := represented
    simp [successor, empty]

/-- Shifting raw identities preserves precisely structural domain equality. -/
theorem identity_exact (state : Cache.State DomainKey) (valid : Cache.Valid state)
    (firstKey secondKey : DomainKey) (first second : Interned DomainKey)
    (firstRep : Represents state firstKey first) (secondRep : Represents state secondKey second) :
    first.identity = second.identity ↔ firstKey = secondKey := by
  by_cases firstEmpty : firstKey = emptyKey
  · have firstZero := (zero_iff state firstKey first firstRep).mpr firstEmpty
    rw [firstZero]
    constructor
    · intro same
      exact firstEmpty.trans ((zero_iff state secondKey second secondRep).mp same.symm).symm
    · intro same
      exact ((zero_iff state secondKey second secondRep).mpr (same.symm.trans firstEmpty)).symm
  · by_cases secondEmpty : secondKey = emptyKey
    · have firstNonzero : first.identity ≠ 0 :=
        fun zero => firstEmpty ((zero_iff state firstKey first firstRep).mp zero)
      have secondZero := (zero_iff state secondKey second secondRep).mpr secondEmpty
      rw [secondZero]
      simp [firstNonzero, show firstKey ≠ secondKey by intro same; exact firstEmpty (same.trans secondEmpty)]
    · obtain ⟨left, leftStored, leftId⟩ := by simpa [Represents, firstEmpty] using firstRep.2
      obtain ⟨right, rightStored, rightId⟩ := by simpa [Represents, secondEmpty] using secondRep.2
      rw [leftId, rightId, Nat.add_right_cancel_iff]
      exact Cache.identity_eq_iff_key_eq state valid leftStored rightStored

/-- Canonical free maps and recursive-pair sets determine the new domain identity. -/
theorem canonical_identity_exact (state : Cache.State DomainKey) (valid : Cache.Valid state)
    (firstKey secondKey : DomainKey) (first second : Interned DomainKey)
    (firstRep : Represents state firstKey first) (secondRep : Represents state secondKey second)
    (firstCanonical : Canonical firstKey) (secondCanonical : Canonical secondKey) :
    first.identity = second.identity ↔ SameDomain firstKey secondKey :=
  (identity_exact state valid firstKey secondKey first second firstRep secondRep).trans
    (canonical_eq_iff firstKey secondKey firstCanonical secondCanonical)

/-- The shifted source identity stays nonnegative only under its shifted machine bound. -/
theorem successor_word_nonnegative (width raw : Nat) (positive : 0 < width)
    (fits : raw + 1 < 2 ^ (width - 1)) :
    (BitVec.ofNat width (raw + 1)).toInt = ((raw + 1 : Nat) : Int) :=
  domain_word_nonnegative width positive (raw + 1) fits

/-- A checked machine successor cannot collide with the reserved zero domain. -/
theorem successor_word_ne_zero (width raw : Nat) (fits : raw + 1 < 2 ^ width) :
    BitVec.ofNat width (raw + 1) ≠ BitVec.ofNat width 0 := by
  intro same
  have equal := domain_word_injective width (raw + 1) 0 fits (by omega) same
  omega

/-- The new domain representation preserves the complete ordered flat memo key. -/
theorem flatKey_exact (width : Nat) (state : Cache.State DomainKey) (valid : Cache.Valid state)
    (firstKey secondKey : DomainKey) (first second : Interned DomainKey)
    (firstRep : Represents state firstKey first) (secondRep : Represents state secondKey second)
    (firstFits : first.identity < 2 ^ width) (secondFits : second.identity < 2 ^ width)
    (firstLeft firstRight secondLeft secondRight : Input)
    (firstLeftSafe : Safe width firstLeft) (firstRightSafe : Safe width firstRight)
    (secondLeftSafe : Safe width secondLeft) (secondRightSafe : Safe width secondRight) :
    flatKey width first firstLeft firstRight = flatKey width second secondLeft secondRight ↔
      (firstKey, firstLeft, firstRight) = (secondKey, secondLeft, secondRight) := by
  constructor
  · intro same
    have components := Prod.mk.inj same
    have operands := Prod.mk.inj components.2
    have domainEqual := (identity_exact state valid firstKey secondKey first second firstRep secondRep).mp
      (domain_word_injective width _ _ firstFits secondFits components.1)
    have leftEqual := (machine_eq_iff width _ _ firstLeftSafe secondLeftSafe).mp operands.1
    have rightEqual := (machine_eq_iff width _ _ firstRightSafe secondRightSafe).mp operands.2
    rw [domainEqual, leftEqual, rightEqual]
  · intro same
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj same
    have domainEqual := (identity_exact state valid firstKey firstKey first second firstRep secondRep).mpr rfl
    simp only [flatKey, domainEqual]

/-- Edge memo keys use the same reserved domain identity with untagged edge identities. -/
theorem edgeKey_exact (width : Nat) (state : Cache.State DomainKey) (valid : Cache.Valid state)
    (firstKey secondKey : DomainKey) (first second : Interned DomainKey)
    (firstRep : Represents state firstKey first) (secondRep : Represents state secondKey second)
    (firstFits : first.identity < 2 ^ width) (secondFits : second.identity < 2 ^ width)
    (firstLeft firstRight secondLeft secondRight : Nat)
    (firstLeftFits : firstLeft < 2 ^ width) (firstRightFits : firstRight < 2 ^ width)
    (secondLeftFits : secondLeft < 2 ^ width) (secondRightFits : secondRight < 2 ^ width) :
    edgeKey width first firstLeft firstRight = edgeKey width second secondLeft secondRight ↔
      (firstKey, firstLeft, firstRight) = (secondKey, secondLeft, secondRight) := by
  constructor
  · intro same
    have components := Prod.mk.inj same
    have operands := Prod.mk.inj components.2
    have domainEqual := (identity_exact state valid firstKey secondKey first second firstRep secondRep).mp
      (domain_word_injective width _ _ firstFits secondFits components.1)
    have leftEqual := domain_word_injective width _ _ firstLeftFits secondLeftFits operands.1
    have rightEqual := domain_word_injective width _ _ firstRightFits secondRightFits operands.2
    rw [domainEqual, leftEqual, rightEqual]
  · intro same
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj same
    have domainEqual := (identity_exact state valid firstKey firstKey first second firstRep secondRep).mpr rfl
    simp only [edgeKey, domainEqual]

end MicroCFTA.IntersectionEmptyDomain
