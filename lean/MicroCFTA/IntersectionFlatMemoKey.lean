import MicroCFTA.IntersectSchedule
import MicroCFTA.InternedConstructorTemplates

/-!
# Tagged machine keys for source intersection memoization

The source stores `4 * identity + tag` in a machine Int and reserves -1
for EmptyNode. Equality is exact under the explicit bit-pattern bounds.
Unresolved reference placeholders bypass the memo table.
-/
namespace MicroCFTA.IntersectionFlatMemoKey
open IntersectSchedule InternedBinderProtocol

/-- Source memoization accepts only complete identities and actual RecInt references. -/
def input : NodeRef → Option Input
  | .empty => some .empty
  | .node identity => some (.node identity)
  | .mu identity => some (.mu identity)
  | .union identity => some (.union identity)
  | .ref (.interned identity) => some (.ref identity)
  | .ref _ => none

/-- The source's constructor tag occupies the two low bits of each nonempty key. -/
def code (width : Nat) : Input → Nat
  | .empty => 2 ^ width - 1
  | .node identity => 4 * identity
  | .mu identity => 4 * identity + 1
  | .union identity => 4 * identity + 2
  | .ref identity => 4 * identity + 3

/-- The exact machine bit pattern produced by each fully interned source input. -/
def machine (width : Nat) (value : Input) : BitVec width := BitVec.ofNat width (code width value)

/-- The actual optional source key includes the placeholder bypass. -/
def key (width : Nat) (value : NodeRef) : Option (BitVec width) := (input value).map (machine width)

/-- Nonempty codes fit below the reserved all-ones sentinel in the first modular period. -/
def Safe (width : Nat) : Input → Prop
  | .empty => True
  | value => code width value < 2 ^ width - 1

/-- Haskell Int multiplication and addition have the represented modular bit pattern. -/
theorem tagged_arithmetic (width identity tag : Nat) :
    (BitVec.ofNat width 4 * BitVec.ofNat width identity + BitVec.ofNat width tag) =
      BitVec.ofNat width (4 * identity + tag) := by
  rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]

/-- EmptyNode uses exactly the signed machine value -1 at each positive word width. -/
theorem empty_signed (width : Nat) (positive : 0 < width) : (machine width .empty).toInt = -1 := by
  have same : machine width .empty = BitVec.allOnes width := by
    apply BitVec.eq_of_toNat_eq
    simp only [machine, code, BitVec.toNat_ofNat, BitVec.toNat_allOnes]
    exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
  rw [same, BitVec.toInt_allOnes, ite_eq_left positive]

/-- A checked machine key retains its complete unwrapped code. -/
theorem machine_exact (width : Nat) (value : Input) (safe : Safe width value) :
    (machine width value).toNat = code width value := by
  have positive := Nat.two_pow_pos width
  have fits : code width value < 2 ^ width := by
    cases value <;> simp only [Safe, code] at safe ⊢ <;> omega
  exact Nat.mod_eq_of_lt fits

/-- Constructor tags and identities are injective before the sentinel and modulo boundary. -/
theorem code_injective (width : Nat) (left right : Input) (leftSafe : Safe width left) (rightSafe : Safe width right)
    (same : code width left = code width right) : left = right := by
  cases left <;> cases right <;> simp only [Safe, code] at leftSafe rightSafe same <;>
    first | rfl | (congr 1; omega) | omega

/-- Key equality is exactly the old tagged-node equality under the explicit machine range. -/
theorem machine_eq_iff (width : Nat) (left right : Input) (leftSafe : Safe width left) (rightSafe : Safe width right) :
    machine width left = machine width right ↔ left = right := by
  constructor
  · intro same
    apply code_injective width left right leftSafe rightSafe
    have observed := congrArg BitVec.toNat same
    simpa only [machine_exact width left leftSafe, machine_exact width right rightSafe] using observed
  · rintro rfl
    rfl

/-- Reading keys as signed Int values preserves exactly the same machine equality. -/
theorem signed_eq_iff (width : Nat) (left right : Input) (leftSafe : Safe width left) (rightSafe : Safe width right) :
    (machine width left).toInt = (machine width right).toInt ↔ left = right := by
  rw [BitVec.toInt_inj, machine_eq_iff width left right leftSafe rightSafe]

/-- Reconstruct the exact tagged source reference of a fully interned schedule input. -/
def source : Input → NodeRef
  | .empty => .empty
  | .node identity => .node identity
  | .mu identity => .mu identity
  | .union identity => .union identity
  | .ref identity => .ref (.interned identity)

/-- Accepted memo inputs reconstruct the original source constructor and reference tag. -/
theorem input_reconstruct (value : NodeRef) (result : Input) (completed : input value = some result) : value = source result := by
  cases value with
  | empty | node | mu | union => cases completed; rfl
  | ref name => cases name <;> cases completed <;> rfl

/-- Accepted memo inputs retain the exact source constructor and reference tags. -/
theorem input_injective (left right : NodeRef) (first second : Input)
    (leftInput : input left = some first) (rightInput : input right = some second) (same : first = second) : left = right := by
  exact (input_reconstruct left first leftInput).trans ((congrArg source same).trans (input_reconstruct right second rightInput).symm)

/-- Equal present memo keys identify the same old source node key within the checked range. -/
theorem key_eq_iff (width : Nat) (left right : NodeRef) (first second : Input)
    (leftInput : input left = some first) (rightInput : input right = some second)
    (leftSafe : Safe width first) (rightSafe : Safe width second) : key width left = key width right ↔ left = right := by
  constructor
  · intro same
    have bits : machine width first = machine width second := by simpa only [key, leftInput, rightInput, Option.map_some, Option.some.injEq] using same
    exact input_injective left right first second leftInput rightInput ((machine_eq_iff width first second leftSafe rightSafe).mp bits)
  · rintro rfl
    rfl

/-- Every non-RecInt placeholder bypasses the source memo table. -/
theorem placeholder_bypass (width : Nat) (name : Reference) (placeholder : ∀ identity, name ≠ .interned identity) :
    key width (.ref name) = none := by
  cases name <;> simp_all [key, input]

/-- The first-period checked range permits negative signed keys and excludes only wraparound and the sentinel. -/
theorem safe_range (bits identity : Nat) :
    (Safe (bits + 2) (.node identity) ↔ identity < 2 ^ bits) ∧
    (Safe (bits + 2) (.mu identity) ↔ identity < 2 ^ bits) ∧
    (Safe (bits + 2) (.union identity) ↔ identity < 2 ^ bits) ∧
    (Safe (bits + 2) (.ref identity) ↔ identity + 1 < 2 ^ bits) := by
  have power : 2 ^ (bits + 2) = 4 * 2 ^ bits := by simp [Nat.pow_add, Nat.mul_comm]
  simp only [Safe, code, power]
  omega

/-- One uniform identity bound makes all four source constructor tags safe. -/
theorem uniform_range (bits identity : Nat) (fits : identity + 1 < 2 ^ bits) :
    Safe (bits + 2) (.node identity) ∧ Safe (bits + 2) (.mu identity) ∧
      Safe (bits + 2) (.union identity) ∧ Safe (bits + 2) (.ref identity) := by
  have ranges := safe_range bits identity
  exact ⟨ranges.1.mpr (by omega), ranges.2.1.mpr (by omega), ranges.2.2.1.mpr (by omega), ranges.2.2.2.mpr fits⟩

/-- The first RecInt key at the sentinel boundary collides with EmptyNode. -/
theorem sentinel_collision (bits : Nat) :
    machine (bits + 2) (.ref (2 ^ bits - 1)) = machine (bits + 2) .empty := by
  have positive := Nat.two_pow_pos bits
  have power : 2 ^ (bits + 2) = 4 * 2 ^ bits := by simp [Nat.pow_add, Nat.mul_comm]
  change BitVec.ofNat _ (4 * (2 ^ bits - 1) + 3) = BitVec.ofNat _ (2 ^ (bits + 2) - 1)
  congr 1
  rw [power]
  omega

/-- After one quarter-word identity period, ordinary node memo keys repeat. -/
theorem node_wrap_collision (bits : Nat) :
    machine (bits + 2) (.node (2 ^ bits)) = machine (bits + 2) (.node 0) := by
  apply BitVec.eq_of_toNat_eq
  have power : 2 ^ (bits + 2) = 4 * 2 ^ bits := by simp [Nat.pow_add, Nat.mul_comm]
  simp [machine, code, BitVec.toNat_ofNat, power]

/-- The 64-bit source key has exact checked collisions well before the identity supply itself wraps. -/
theorem collisions64 :
    key 64 (.ref (.interned 4611686018427387903)) = key 64 .empty ∧
    key 64 (.node 4611686018427387904) = key 64 (.node 0) ∧
    (NodeRef.ref (.interned 4611686018427387903)) ≠ .empty ∧
    (NodeRef.node 4611686018427387904) ≠ .node 0 := by
  exact ⟨congrArg some (sentinel_collision 62), congrArg some (node_wrap_collision 62), by decide, by decide⟩

end MicroCFTA.IntersectionFlatMemoKey
