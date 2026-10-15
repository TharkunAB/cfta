import MicroCFTA.Cache

/-!
# Canonical identities across independent allocation histories

The two tables can reserve different identities and retain different extra
keys. Shared stored keys determine a partial identity correspondence.
Canonical identity validity makes this correspondence one-to-one. Existing
pairs survive table growth, including arbitrary permitted atomic steps.
-/
namespace MicroCFTA.CacheRenaming
open Cache
variable {Key : Type} {first second after firstAfter secondAfter : State Key}

/-- The second table contains every key stored in the first table. -/
def Covers (first second : State Key) : Prop :=
  ∀ key entry, first.table key = some entry → ∃ other, second.table key = some other

/-- Two canonical identities name one complete physical key in the two tables. -/
def Linked (first second : State Key) (left right : Nat) : Prop :=
  ∃ key firstEntry secondEntry, first.table key = some firstEntry ∧
    second.table key = some secondEntry ∧ firstEntry.identity = left ∧ secondEntry.identity = right

/-- A table covers itself without an identity allocation premise. -/
theorem covers_refl (state : State Key) : Covers state state :=
  fun _ entry stored => ⟨entry, stored⟩

/-- Extra entries in the second table retain coverage of the first table. -/
theorem Covers.grows (covered : Covers first second) (growth : Extends second.table after.table) :
    Covers first after := by
  intro key entry stored
  obtain ⟨other, present⟩ := covered key entry stored
  exact ⟨other, growth key other present⟩

/-- Growing either table preserves every earlier identity pair. -/
theorem Linked.grows (linked : Linked first second left right)
    (firstGrowth : Extends first.table firstAfter.table) (secondGrowth : Extends second.table secondAfter.table) :
    Linked firstAfter secondAfter left right := by
  obtain ⟨key, firstEntry, secondEntry, firstStored, secondStored, firstId, secondId⟩ := linked
  exact ⟨key, firstEntry, secondEntry, firstGrowth _ _ firstStored, secondGrowth _ _ secondStored, firstId, secondId⟩

/-- A covered stored identity has a corresponding canonical identity in the second table. -/
theorem linked_exists (covered : Covers first second) (stored : first.table key = some entry) :
    ∃ identity, Linked first second entry.identity identity := by
  obtain ⟨other, present⟩ := covered key entry stored
  exact ⟨other.identity, key, entry, other, stored, present, rfl, rfl⟩

/-- A valid pair of tables preserves both directions of equality between shared identities. -/
theorem linked_eq_iff (firstValid : Valid first) (secondValid : Valid second)
    (left : Linked first second a b) (right : Linked first second c d) : a = c ↔ b = d := by
  obtain ⟨firstKey, firstA, secondB, storedA, storedB, rfl, rfl⟩ := left
  obtain ⟨secondKey, firstC, secondD, storedC, storedD, rfl, rfl⟩ := right
  exact (identity_eq_iff_key_eq first firstValid storedA storedC).trans
    (identity_eq_iff_key_eq second secondValid storedB storedD).symm

/-- One source identity has at most one corresponding identity in a valid second table. -/
theorem linked_functional (firstValid : Valid first) (secondValid : Valid second)
    (left : Linked first second a b) (right : Linked first second a c) : b = c :=
  (linked_eq_iff firstValid secondValid left right).mp rfl

/-- One target identity has at most one corresponding identity in a valid first table. -/
theorem linked_injective (firstValid : Valid first) (secondValid : Valid second)
    (left : Linked first second a c) (right : Linked first second b c) : a = b :=
  (linked_eq_iff firstValid secondValid left right).mpr rfl

/-- Sequential interning changes no lookup at a different physical key. -/
theorem intern_other [DecidableEq Key] (state : State Key) (key other : Key) (different : other ≠ key) :
    (intern state key).2.table other = state.table other := by
  cases found : state.table key with
  | some entry => simp [intern, found]
  | none => simp [intern, found, install, keepFirst, reserve, put, different]

/-- Sequential interning retains every existing canonical table entry. -/
theorem intern_extends [DecidableEq Key] (state : State Key) (key : Key) :
    Extends state.table (intern state key).2.table := by
  intro other entry stored
  by_cases same : other = key
  · subst other
    simp [intern, stored]
  · rw [intern_other state key other same]
    exact stored

/-- Interning one shared key preserves coverage despite different earlier allocation histories. -/
theorem covers_intern [DecidableEq Key] (first second : State Key) (covered : Covers first second)
    (secondValid : Valid second) (key : Key) : Covers (intern first key).2 (intern second key).2 := by
  intro other entry stored
  by_cases same : other = key
  · subst other
    exact ⟨(intern second key).1, (intern_correct second key secondValid).2.1⟩
  · have earlier : first.table other = some entry := by rw [← intern_other first key other same]; exact stored
    obtain ⟨otherEntry, present⟩ := covered other entry earlier
    exact ⟨otherEntry, intern_extends second key other otherEntry present⟩

/-- Actual shared-key interning produces corresponding stored identities without equal counters. -/
theorem linked_intern [DecidableEq Key] (first second : State Key)
    (firstValid : Valid first) (secondValid : Valid second) (key : Key) :
    Linked (intern first key).2 (intern second key).2 (intern first key).1.identity (intern second key).1.identity :=
  ⟨key, (intern first key).1, (intern second key).1,
    (intern_correct first key firstValid).2.1, (intern_correct second key secondValid).2.1, rfl, rfl⟩

/-- Arbitrary permitted atomic activity in the second table preserves coverage. -/
theorem Covers.steps [DecidableEq Key] (covered : Covers first second) (steps : Steps second after) :
    Covers first after := covered.grows (steps_table_extends steps)

/-- Independent valid atomic histories preserve every shared stored identity pair. -/
theorem Linked.steps [DecidableEq Key] (linked : Linked first second left right)
    (firstSteps : Steps first firstAfter) (secondSteps : Steps second secondAfter) :
    Linked firstAfter secondAfter left right :=
  linked.grows (steps_table_extends firstSteps) (steps_table_extends secondSteps)

end MicroCFTA.CacheRenaming
