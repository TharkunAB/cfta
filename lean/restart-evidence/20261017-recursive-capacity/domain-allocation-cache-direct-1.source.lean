import MicroCFTA.Cache

/-!
# Finite sequential interning

The trace records actual sequential calls to `Cache.intern`.
Each miss removes at least one key from the remaining inventory.
Repeated hits do not consume another identity.
-/

namespace MicroCFTA.CacheFiniteInterning

open Cache

variable {Key : Type}

/-- Count inventory occurrences that have no current table entry. -/
def missing : List Key → State Key → Nat
  | [], _ => 0
  | key :: rest, state =>
      (if (state.table key).isNone then 1 else 0) + missing rest state

/-- The remaining count does not exceed the original inventory length. -/
theorem missing_le_length (inventory : List Key) (state : State Key) :
    missing inventory state ≤ inventory.length := by
  induction inventory with
  | nil => simp [missing]
  | cons key rest ih =>
    cases state.table key <;> simp_all [missing] <;> omega

/-- Table growth cannot increase the remaining count. -/
theorem missing_mono (inventory : List Key) {before after : State Key}
    (growth : Extends before.table after.table) :
    missing inventory after ≤ missing inventory before := by
  induction inventory with
  | nil => simp [missing]
  | cons key rest ih =>
    cases lookup : before.table key with
    | none =>
      cases after.table key <;> simp_all [missing] <;> omega
    | some value =>
      have present := growth key value lookup
      simpa [missing, lookup, present] using ih

variable [DecidableEq Key]

/-- A sequential interning call retains every earlier table entry. -/
theorem intern_extends (state : State Key) (key : Key) :
    Extends state.table (intern state key).2.table := by
  cases lookup : state.table key with
  | some value => simpa [intern, lookup] using extends_refl state.table
  | none =>
    simpa [intern, lookup, reserve, install] using
      keepFirst_extends state.table key (⟨state.next, key⟩ : Interned Key)

/-- The requested key is present after the actual sequential call. -/
theorem intern_present (state : State Key) (key : Key) :
    ∃ value, (intern state key).2.table key = some value := by
  cases lookup : state.table key with
  | some value => exact ⟨value, by simp [intern, lookup]⟩
  | none => simp [intern, lookup, reserve, install, keepFirst, put]

/-- The supply increases exactly on a sequential miss. -/
theorem intern_next (state : State Key) (key : Key) :
    (intern state key).2.next = state.next +
      (if (state.table key).isNone then 1 else 0) := by
  cases lookup : state.table key <;> simp [intern, lookup, reserve, install]

/-- An existing key returns its entry and the entire unchanged state. -/
theorem intern_hit {state : State Key} {key : Key} {value : Interned Key}
    (present : state.table key = some value) : intern state key = (value, state) := by
  simp [intern, present]

/-- A miss removes at least one inventory occurrence. -/
theorem missing_drop (inventory : List Key) (state : State Key) (key : Key)
    (member : key ∈ inventory) (absent : state.table key = none) :
    missing inventory (intern state key).2 + 1 ≤ missing inventory state := by
  induction inventory with
  | nil => simp at member
  | cons first rest ih =>
    by_cases same : first = key
    · subst first
      obtain ⟨value, present⟩ := intern_present state key
      have smaller := missing_mono rest (intern_extends state key)
      simpa [missing, absent, present] using Nat.add_le_add_right smaller 1
    · have tailMember : key ∈ rest := by simpa [List.mem_cons, Ne.symm same] using member
      have smaller := ih tailMember
      have unchanged : (intern state key).2.table first = state.table first := by
        simp [intern, absent, reserve, install, keepFirst, put, same]
      simp only [missing, unchanged]
      omega

/-- One actual call preserves the supply plus remaining-key potential. -/
theorem intern_potential (inventory : List Key) (state : State Key) (key : Key)
    (member : key ∈ inventory) :
    (intern state key).2.next + missing inventory (intern state key).2 ≤
      state.next + missing inventory state := by
  cases lookup : state.table key with
  | some value => simp [intern, lookup]
  | none =>
    have smaller := missing_drop inventory state key member lookup
    rw [intern_next]
    simp only [lookup, Option.isNone_none, ↓reduceIte]
    omega

/-- Every trace step executes one literal sequential interning call. -/
inductive Trace (inventory : List Key) : State Key → State Key → Prop where
  | refl (state : State Key) : Trace inventory state state
  | intern (earlier : Trace inventory before middle) (key : Key)
      (member : key ∈ inventory) : Trace inventory before (Cache.intern middle key).2

/-- Sequential trace composition retains the actual intermediate state. -/
theorem Trace.trans (first : Trace inventory before middle)
    (last : Trace inventory middle after) : Trace inventory before after := by
  induction last with
  | refl => exact first
  | intern _ key member ih => exact .intern ih key member

/-- Actual calls preserve canonical cache validity. -/
theorem Trace.valid (trace : Trace inventory before after) (valid : Valid before) :
    Valid after := by
  induction trace with
  | refl => exact valid
  | intern _ key _ ih => exact (intern_correct _ key ih).1

/-- All earlier entries remain present throughout a sequential trace. -/
theorem Trace.extends (trace : Trace inventory before after) :
    Extends before.table after.table := by
  induction trace with
  | refl => exact extends_refl _
  | intern _ key _ ih => exact extends_trans ih (intern_extends _ key)

/-- Repeated calls cannot spend the same missing-key credit twice. -/
theorem Trace.potential (trace : Trace inventory before after) :
    after.next + missing inventory after ≤ before.next + missing inventory before := by
  induction trace with
  | refl => exact Nat.le_refl _
  | intern _ key member ih =>
    exact (intern_potential inventory _ key member).trans ih

/-- Only keys missing from the initial table can increase the supply. -/
theorem Trace.next_le_missing (trace : Trace inventory before after) :
    after.next ≤ before.next + missing inventory before := by
  have bounded := trace.potential
  omega

/-- The bound depends on the static inventory, not the number of calls. -/
theorem Trace.next_le (trace : Trace inventory before after) :
    after.next ≤ before.next + inventory.length := by
  exact trace.next_le_missing.trans (Nat.add_le_add_left (missing_le_length inventory before) _)

end MicroCFTA.CacheFiniteInterning
