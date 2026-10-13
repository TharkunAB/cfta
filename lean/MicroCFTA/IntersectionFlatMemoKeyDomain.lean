import MicroCFTA.IntersectionFlatMemoKey

/-!
# Canonical domain identities and flat intersection keys

The domain cache interns the exact ordered free-map and recursive-pair
lists. Its canonical identity replaces that structural component of each
old memo key. Explicit word bounds preserve equality of the new triple.
-/
namespace MicroCFTA.IntersectionFlatMemoKeyDomain
open Cache IntersectSchedule InternedBinderProtocol IntersectionFlatMemoKey

/-- The exact structural key supplied to the source intersection-domain interning cache. -/
structure DomainKey where
  free : List (Nat × NodeRef)
  seen : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- Source set entries use the lexicographic order of canonical IntersectId pairs. -/
def pairLess (left right : Nat × Nat) : Prop := left.1 < right.1 ∨ (left.1 = right.1 ∧ left.2 < right.2)

/-- IntMap.toList and Set.toList retain unique entries in increasing key order. -/
def Canonical (domain : DomainKey) : Prop :=
  domain.free.Pairwise (fun left right => left.1 < right.1) ∧ domain.seen.Pairwise pairLess

/-- Two source domains retain the same free bindings and the same recursive intersection pairs. -/
def SameDomain (left right : DomainKey) : Prop :=
  (∀ binding, binding ∈ left.free ↔ binding ∈ right.free) ∧
    (∀ pair, pair ∈ left.seen ↔ pair ∈ right.seen)

/-- Unique ordered structural lists are determined by their entries. -/
theorem ordered_entries_exact (less : Item → Item → Prop)
    (irreflexive : ∀ item, ¬ less item item) (asymmetric : ∀ left right, less left right → less right left → False)
    (left right : List Item) (leftOrdered : left.Pairwise less) (rightOrdered : right.Pairwise less)
    (entries : ∀ item, item ∈ left ↔ item ∈ right) : left = right := by
  have leftUnique : left.Nodup := by
    apply leftOrdered.imp
    intro a b before same
    subst b
    exact irreflexive a before
  have rightUnique : right.Nodup := by
    apply rightOrdered.imp
    intro a b before same
    subst b
    exact irreflexive a before
  exact List.Perm.eq_of_pairwise (fun a b _ _ first second => False.elim (asymmetric a b first second))
    leftOrdered rightOrdered ((List.perm_ext_iff_of_nodup leftUnique rightUnique).mpr entries)

/-- Canonical source domain keys are equal exactly when their maps and sets have the same entries. -/
theorem canonical_eq_iff (left right : DomainKey) (leftCanonical : Canonical left) (rightCanonical : Canonical right) :
    left = right ↔ SameDomain left right := by
  constructor
  · rintro rfl
    exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · intro same
    have free := ordered_entries_exact (fun a b : Nat × NodeRef => a.1 < b.1)
      (fun _ => by omega) (fun _ _ _ _ => by omega) left.free right.free leftCanonical.1 rightCanonical.1 same.1
    have seen := ordered_entries_exact pairLess (fun _ => by simp [pairLess])
      (fun _ _ _ _ => by simp only [pairLess] at *; omega)
      left.seen right.seen leftCanonical.2 rightCanonical.2 same.2
    cases left
    cases right
    cases free
    cases seen
    rfl

/-- Actual domain interning retains the full structural key and installs its returned identity. -/
theorem domain_intern_correct (state : Cache.State DomainKey) (valid : Cache.Valid state) (key : DomainKey) :
    Cache.Valid (Cache.intern state key).2 ∧
      (Cache.intern state key).2.table key = some (Cache.intern state key).1 ∧
      (Cache.intern state key).1.key = key := Cache.intern_correct state key valid

/-- Interned source domain identity is equivalent to structural canonical-domain equality. -/
theorem domain_identity_exact (state : Cache.State DomainKey) (valid : Cache.Valid state)
    (leftKey rightKey : DomainKey) (left right : Interned DomainKey)
    (leftStored : state.table leftKey = some left) (rightStored : state.table rightKey = some right)
    (leftCanonical : Canonical leftKey) (rightCanonical : Canonical rightKey) :
    left.identity = right.identity ↔ SameDomain leftKey rightKey :=
  (Cache.identity_eq_iff_key_eq state valid leftStored rightStored).trans
    (canonical_eq_iff leftKey rightKey leftCanonical rightCanonical)

/-- A flat memo entry uses domain identity followed by the two ordered operand keys. -/
abbrev Triple (width : Nat) := BitVec width × BitVec width × BitVec width

/-- Complete inputs select the new flat source key without reordering its operands. -/
def flatKey (width : Nat) (domain : Interned DomainKey) (left right : Input) : Triple width :=
  (BitVec.ofNat width domain.identity, machine width left, machine width right)

/-- A source domain identity remains a nonnegative signed machine key within its supply bound. -/
theorem domain_word_nonnegative (width : Nat) (positive : 0 < width) (identity : Nat)
    (fits : identity < 2 ^ (width - 1)) :
    (BitVec.ofNat width identity).toInt = (identity : Int) := by
  exact BitVec.toInt_ofInt_eq_self (n := (identity : Int)) positive
    (by have := Int.pow_nonneg (show (0 : Int) ≤ 2 by omega) (m := width - 1); omega)
    (by exact_mod_cast fits)

/-- Checked domain identity casts are injective even before imposing the stronger nonnegative first-key bound. -/
theorem domain_word_injective (width left right : Nat) (leftFits : left < 2 ^ width) (rightFits : right < 2 ^ width)
    (same : BitVec.ofNat width left = BitVec.ofNat width right) : left = right := by
  have observed := congrArg BitVec.toNat same
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits] using observed

/-- The flat triple preserves exactly the old structural-domain and tagged-operand key equality. -/
theorem flatKey_eq_iff (width : Nat) (state : Cache.State DomainKey) (valid : Cache.Valid state)
    (firstKey secondKey : DomainKey) (firstDomain secondDomain : Interned DomainKey)
    (firstStored : state.table firstKey = some firstDomain) (secondStored : state.table secondKey = some secondDomain)
    (firstDomainFits : firstDomain.identity < 2 ^ width) (secondDomainFits : secondDomain.identity < 2 ^ width)
    (firstLeft firstRight secondLeft secondRight : Input)
    (firstLeftSafe : Safe width firstLeft) (firstRightSafe : Safe width firstRight)
    (secondLeftSafe : Safe width secondLeft) (secondRightSafe : Safe width secondRight) :
    flatKey width firstDomain firstLeft firstRight = flatKey width secondDomain secondLeft secondRight ↔
      (firstKey, firstLeft, firstRight) = (secondKey, secondLeft, secondRight) := by
  constructor
  · intro equal
    have components := Prod.mk.inj equal
    have operands := Prod.mk.inj components.2
    have domainEqual := (Cache.identity_eq_iff_key_eq state valid firstStored secondStored).mp
      (domain_word_injective width _ _ firstDomainFits secondDomainFits components.1)
    have leftEqual := (machine_eq_iff width _ _ firstLeftSafe secondLeftSafe).mp operands.1
    have rightEqual := (machine_eq_iff width _ _ firstRightSafe secondRightSafe).mp operands.2
    rw [domainEqual, leftEqual, rightEqual]
  · intro equal
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj equal
    have domainEqual := (Cache.identity_eq_iff_key_eq state valid firstStored secondStored).mpr rfl
    simp only [flatKey, domainEqual]

/-- A memo hit under the new flat key returns the value of the same old structural request. -/
theorem memo_hit_correct (width : Nat) (state : Cache.State DomainKey) (valid : Cache.Valid state)
    (firstKey secondKey : DomainKey) (firstDomain secondDomain : Interned DomainKey)
    (firstStored : state.table firstKey = some firstDomain) (secondStored : state.table secondKey = some secondDomain)
    (firstDomainFits : firstDomain.identity < 2 ^ width) (secondDomainFits : secondDomain.identity < 2 ^ width)
    (firstLeft firstRight secondLeft secondRight : Input)
    (firstLeftSafe : Safe width firstLeft) (firstRightSafe : Safe width firstRight)
    (secondLeftSafe : Safe width secondLeft) (secondRightSafe : Safe width secondRight)
    (compute : DomainKey × Input × Input → Output)
    (same : flatKey width firstDomain firstLeft firstRight = flatKey width secondDomain secondLeft secondRight) :
    compute (firstKey, firstLeft, firstRight) = compute (secondKey, secondLeft, secondRight) :=
  congrArg compute ((flatKey_eq_iff width state valid firstKey secondKey firstDomain secondDomain firstStored secondStored
    firstDomainFits secondDomainFits firstLeft firstRight secondLeft secondRight firstLeftSafe firstRightSafe secondLeftSafe secondRightSafe).mp same)

/-- The source wrapper builds no flat key if either operand is an unresolved placeholder. -/
def sourceKey (width : Nat) (domain : Interned DomainKey) (left right : NodeRef) : Option (Triple width) := do
  let leftKey ← key width left
  let rightKey ← key width right
  pure (BitVec.ofNat width domain.identity, leftKey, rightKey)

/-- Any unresolved left placeholder bypasses flat lookup and insertion. -/
theorem left_placeholder_bypass (width : Nat) (domain : Interned DomainKey) (name : Reference) (right : NodeRef)
    (placeholder : ∀ identity, name ≠ .interned identity) : sourceKey width domain (.ref name) right = none := by
  simp only [sourceKey, placeholder_bypass width name placeholder, Bind.bind, Option.bind]

/-- Any unresolved right placeholder bypasses flat lookup and insertion. -/
theorem right_placeholder_bypass (width : Nat) (domain : Interned DomainKey) (left : NodeRef) (name : Reference)
    (placeholder : ∀ identity, name ≠ .interned identity) : sourceKey width domain left (.ref name) = none := by
  simp only [sourceKey, placeholder_bypass width name placeholder]
  cases key width left <;> rfl

/-- The source wrapper uses the proved flat triple whenever both operand identities are complete. -/
theorem sourceKey_complete (width : Nat) (domain : Interned DomainKey) (left right : NodeRef) (first second : Input)
    (leftInput : input left = some first) (rightInput : input right = some second) :
    sourceKey width domain left right = some (flatKey width domain first second) := by
  simp only [sourceKey, key, leftInput, rightInput, Option.map_some, Bind.bind, Option.bind, flatKey, pure]

/-- Edge intersection uses the domain identity and the two raw edge identities. -/
def edgeKey (width : Nat) (domain : Interned DomainKey) (left right : Nat) : Triple width :=
  (BitVec.ofNat width domain.identity, BitVec.ofNat width left, BitVec.ofNat width right)

/-- The new edge triple preserves its old structural-domain and ordered-edge key without identity wraparound. -/
theorem edgeKey_eq_iff (width : Nat) (state : Cache.State DomainKey) (valid : Cache.Valid state)
    (firstKey secondKey : DomainKey) (firstDomain secondDomain : Interned DomainKey)
    (firstStored : state.table firstKey = some firstDomain) (secondStored : state.table secondKey = some secondDomain)
    (firstDomainFits : firstDomain.identity < 2 ^ width) (secondDomainFits : secondDomain.identity < 2 ^ width)
    (firstLeft firstRight secondLeft secondRight : Nat)
    (firstLeftFits : firstLeft < 2 ^ width) (firstRightFits : firstRight < 2 ^ width)
    (secondLeftFits : secondLeft < 2 ^ width) (secondRightFits : secondRight < 2 ^ width) :
    edgeKey width firstDomain firstLeft firstRight = edgeKey width secondDomain secondLeft secondRight ↔
      (firstKey, firstLeft, firstRight) = (secondKey, secondLeft, secondRight) := by
  constructor
  · intro equal
    have components := Prod.mk.inj equal
    have operands := Prod.mk.inj components.2
    have domainEqual := (Cache.identity_eq_iff_key_eq state valid firstStored secondStored).mp
      (domain_word_injective width _ _ firstDomainFits secondDomainFits components.1)
    have leftEqual := domain_word_injective width _ _ firstLeftFits secondLeftFits operands.1
    have rightEqual := domain_word_injective width _ _ firstRightFits secondRightFits operands.2
    rw [domainEqual, leftEqual, rightEqual]
  · intro equal
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj equal
    have domainEqual := (Cache.identity_eq_iff_key_eq state valid firstStored secondStored).mpr rfl
    simp only [edgeKey, domainEqual]

end MicroCFTA.IntersectionFlatMemoKeyDomain
