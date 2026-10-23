import Std

/-!
# Interning and memo-table invariants

This module models the effective key lookup of `Interned/Cache.hs` and
`Interned/Memo.hs`. Atomic updates are individual trace steps. Reads may occur
after any finite sequence of other updates. Hash-table storage, memory
ordering, runtime type casts and evaluation of recursive thunks require a
separate implementation correspondence.
-/

namespace MicroCFTA.Cache

/-- A typed table interface. -/
abbrev Table (Key Value : Type) := Key → Option Value

/-- Store one key without changing the other entries. -/
def put [DecidableEq Key] (table : Table Key Value) (key : Key) (value : Value) : Table Key Value :=
  fun other => if other = key then some value else table other

/-- The atomic first-writer update in `insertHashed`. -/
def keepFirst [DecidableEq Key] (table : Table Key Value) (key : Key) (candidate : Value) : Table Key Value :=
  match table key with
  | some _ => table
  | none => put table key candidate

/-- Table growth preserves all previously stored entries. -/
def Extends (before after : Table Key Value) : Prop :=
  ∀ key value, before key = some value → after key = some value

theorem extends_refl (table : Table Key Value) : Extends table table := fun _ _ h => h

theorem extends_trans (first : Extends before middle) (second : Extends middle after) :
    Extends before after := fun key value h => second key value (first key value h)

/-- An atomic insertion never changes a previously stored value. -/
theorem keepFirst_extends [DecidableEq Key] (table : Table Key Value) (key : Key) (candidate : Value) :
    Extends table (keepFirst table key candidate) := by
  intro other value original
  cases lookup : table key with
  | some existing => simpa [keepFirst, lookup] using original
  | none =>
    have different : other ≠ key := by intro same; subst other; simp_all
    simpa [keepFirst, lookup, put, different] using original

/-- An atomic insertion leaves the requested key present. -/
theorem keepFirst_present [DecidableEq Key] (table : Table Key Value) (key : Key) (candidate : Value) :
    ∃ stored, keepFirst table key candidate key = some stored := by
  cases lookup : table key <;> simp [keepFirst, lookup, put]

/-- A present key retains its original value. -/
theorem keepFirst_existing [DecidableEq Key] {table : Table Key Value} {key : Key} {stored : Value}
    (present : table key = some stored) (candidate : Value) :
    keepFirst table key candidate key = some stored := by
  rw [keepFirst, present]
  exact present

/-- Repeating an insertion is idempotent, even with a different candidate. -/
theorem keepFirst_idempotent [DecidableEq Key] (table : Table Key Value) (key : Key) (first second : Value) :
    keepFirst (keepFirst table key first) key second = keepFirst table key first := by
  obtain ⟨stored, present⟩ := keepFirst_present table key first
  rw [keepFirst, present]

/-- A finite sequence of arbitrary atomic first-writer updates. -/
def updates [DecidableEq Key] (table : Table Key Value) : List (Key × Value) → Table Key Value
  | [] => table
  | (key, value) :: rest => updates (keepFirst table key value) rest

/-- Arbitrary intervening inserts preserve every completed earlier insert. -/
theorem updates_extend [DecidableEq Key] (table : Table Key Value) (trace : List (Key × Value)) :
    Extends table (updates table trace) := by
  induction trace generalizing table with
  | nil => exact extends_refl table
  | cons entry rest ih => exact extends_trans (keepFirst_extends table entry.1 entry.2) (ih _)

/-- A read after insertion sees its winner even after other threads insert. -/
theorem delayed_read [DecidableEq Key] (table : Table Key Value) (key : Key) (candidate : Value)
    (trace : List (Key × Value)) :
    ∃ stored, keepFirst table key candidate key = some stored ∧
      updates (keepFirst table key candidate) trace key = some stored := by
  obtain ⟨stored, present⟩ := keepFirst_present table key candidate
  exact ⟨stored, present, updates_extend _ trace key stored present⟩

/-- Two completed reads for one stored key agree throughout a growing table. -/
theorem reads_agree (growth : Extends before after)
    (first : before key = some left) (second : after key = some right) : left = right := by
  have same := (growth key left first).symm.trans second
  cases same
  rfl

/-- The final lookup cannot use the fallback after a completed insert. -/
theorem readback_fallback_unused [DecidableEq Key] (table : Table Key Value) (key : Key)
    (candidate fallback : Value) (trace : List (Key × Value)) :
    (updates (keepFirst table key candidate) trace key).getD fallback =
      (updates (keepFirst table key candidate) trace key).getD candidate := by
  obtain ⟨stored, _, present⟩ := delayed_read table key candidate trace
  simp [present]

/-- A cache contains only results of its designated pure function. -/
def MemoValid (compute : Key → Value) (table : Table Key Value) : Prop :=
  ∀ key value, table key = some value → value = compute key

/-- Inserting a pure result preserves the memo invariant. -/
theorem keepFirst_memo [DecidableEq Key] (compute : Key → Value) (valid : MemoValid compute table) (key : Key) :
    MemoValid compute (keepFirst table key (compute key)) := by
  intro other value present
  cases lookup : table key with
  | some existing => exact valid other value (by simpa [keepFirst, lookup] using present)
  | none =>
    by_cases same : other = key
    · subst other
      simpa [keepFirst, lookup, put] using present.symm
    · exact valid other value (by simpa [keepFirst, lookup, put, same] using present)

/-- Memoized lookup returns the pure function's value. -/
theorem memo_correct [DecidableEq Key] (compute : Key → Value) (valid : MemoValid compute table) (key : Key) :
    (keepFirst table key (compute key) key).getD (compute key) = compute key := by
  obtain ⟨stored, present⟩ := keepFirst_present table key (compute key)
  have same := keepFirst_memo compute valid key key stored present
  simp [present, same]

/-- A canonical interned entry retains both its identity and its structural key. -/
structure Interned (Key : Type) where
  identity : Nat
  key : Key
deriving DecidableEq

/-- The identity supply records issued candidates, including candidates that lose races. -/
structure State (Key : Type) where
  next : Nat
  issued : Nat → Option Key
  table : Table Key (Interned Key)

/-- Every table entry has its own key and an identity reserved for that key. -/
def Valid (state : State Key) : Prop :=
  (∀ ident key, state.issued ident = some key → ident < state.next) ∧
  (∀ key value, state.table key = some value →
    value.key = key ∧ state.issued value.identity = some key)

/-- Reserve the next identity. This models the atomic fetch-and-add step. -/
def reserve (state : State Key) (key : Key) : Interned Key × State Key :=
  (⟨state.next, key⟩,
    {state with
      next := state.next + 1
      issued := fun ident => if ident = state.next then some key else state.issued ident})

/-- Reserving an identity preserves every earlier reservation. -/
theorem reserve_extends (state : State Key) (key : Key) (valid : Valid state) :
    Extends state.issued (reserve state key).2.issued := by
  intro ident old present
  have lt := valid.1 ident old present
  simp [reserve, show ident ≠ state.next by omega, present]

/-- The reserved candidate belongs to the resulting supply. -/
theorem reserve_issued (state : State Key) (key : Key) :
    (reserve state key).2.issued (reserve state key).1.identity = some key := by
  simp [reserve]

/-- A fresh reservation preserves identity and structural-key validity. -/
theorem reserve_valid (state : State Key) (key : Key) (valid : Valid state) : Valid (reserve state key).2 := by
  constructor
  · intro ident other present
    by_cases same : ident = state.next
    · simp [reserve]; omega
    · have old : state.issued ident = some other := by simpa [reserve, same] using present
      have lt := valid.1 ident other old
      simp [reserve]; omega
  · intro other value present
    obtain ⟨keyMatches, issued⟩ := valid.2 other value present
    exact ⟨keyMatches, reserve_extends state key valid value.identity other issued⟩

/-- The atomic insertion of a previously reserved candidate. -/
def install [DecidableEq Key] (state : State Key) (candidate : Interned Key) : State Key :=
  {state with table := keepFirst state.table candidate.key candidate}

/-- Any correctly reserved candidate is safe to install, even after later reservations. -/
theorem install_valid [DecidableEq Key] (state : State Key) (candidate : Interned Key)
    (valid : Valid state) (issued : state.issued candidate.identity = some candidate.key) :
    Valid (install state candidate) := by
  refine ⟨valid.1, ?_⟩
  intro key value present
  cases lookup : state.table candidate.key with
  | some existing => exact valid.2 key value (by simpa [install, keepFirst, lookup] using present)
  | none =>
    by_cases same : key = candidate.key
    · subst key
      have equal : candidate = value := by simpa [install, keepFirst, lookup, put] using present
      subst value
      exact ⟨rfl, issued⟩
    · exact valid.2 key value (by simpa [install, keepFirst, lookup, put, same] using present)

/-- Two stored structures have the same identity exactly when their keys agree. -/
theorem identity_eq_iff_key_eq (state : State Key) (valid : Valid state)
    (left : state.table leftKey = some leftValue) (right : state.table rightKey = some rightValue) :
    leftValue.identity = rightValue.identity ↔ leftKey = rightKey := by
  constructor
  · intro same
    have hl := (valid.2 leftKey leftValue left).2
    have hr := (valid.2 rightKey rightValue right).2
    rw [same] at hl
    have equal := hl.symm.trans hr
    cases equal
    rfl
  · intro same
    subst rightKey
    have equal := left.symm.trans right
    cases equal
    rfl

/-- A sequential miss reserves an identity and performs the first-writer update. -/
def intern [DecidableEq Key] (state : State Key) (key : Key) : Interned Key × State Key :=
  match state.table key with
  | some found => (found, state)
  | none =>
    let (candidate, reserved) := reserve state key
    let installed := install reserved candidate
    ((installed.table key).getD candidate, installed)

/-- Empty interning state has no issued identities or table entries. -/
def emptyState : State Key := ⟨0, fun _ => none, fun _ => none⟩

theorem empty_valid : Valid (emptyState (Key := Key)) := by
  constructor <;> intro key value impossible <;> cases impossible

/-- Sequential interning returns a stored entry and preserves canonical identity. -/
theorem intern_correct [DecidableEq Key] (state : State Key) (key : Key) (valid : Valid state) :
    Valid (intern state key).2 ∧
      (intern state key).2.table key = some (intern state key).1 ∧
      (intern state key).1.key = key := by
  cases lookup : state.table key with
  | some found =>
    simpa [intern, lookup] using And.intro valid (And.intro lookup (valid.2 key found lookup).1)
  | none =>
    have reservedValid := reserve_valid state key valid
    have installedValid := install_valid (reserve state key).2 (reserve state key).1
      reservedValid (reserve_issued state key)
    have present : (install (reserve state key).2 (reserve state key).1).table key =
        some (reserve state key).1 := by
      simp [install, reserve, keepFirst, lookup, put]
    simp only [intern, lookup]
    change Valid (install (reserve state key).2 (reserve state key).1) ∧ _
    rw [present]
    exact ⟨installedValid, rfl, rfl⟩

/-- A later lookup returns the same canonical value without another reservation. -/
theorem intern_idempotent [DecidableEq Key] (state : State Key) (key : Key) (valid : Valid state) :
    intern (intern state key).2 key = intern state key := by
  have stored := (intern_correct state key valid).2.1
  rw [intern, stored]

/-- Atomic reserve and install steps may occur in any order consistent with reservations. -/
inductive Step [DecidableEq Key] : State Key → State Key → Prop where
  | reserve (state : State Key) (key : Key) : Step state (reserve state key).2
  | install (state : State Key) (candidate : Interned Key)
      (issued : state.issued candidate.identity = some candidate.key) : Step state (install state candidate)

/-- A finite interleaving of atomic steps from any number of callers. -/
inductive Steps [DecidableEq Key] : State Key → State Key → Prop where
  | refl (state : State Key) : Steps state state
  | next (earlier : Steps before middle) (step : Step middle after) : Steps before after

/-- Every permitted atomic step preserves canonical identity. -/
theorem step_valid [DecidableEq Key] {before after : State Key}
    (valid : Valid before) (step : Step before after) : Valid after := by
  cases step with
  | reserve key => exact reserve_valid _ key valid
  | install candidate issued => exact install_valid _ candidate valid issued

/-- Every finite interleaving preserves the interning invariant. -/
theorem steps_valid [DecidableEq Key] {before after : State Key}
    (valid : Valid before) (trace : Steps before after) : Valid after := by
  induction trace with
  | refl => exact valid
  | next earlier step ih => exact step_valid ih step

/-- Table contents never change once installed, through arbitrary interleavings. -/
theorem steps_table_extends [DecidableEq Key] {before after : State Key}
    (trace : Steps before after) : Extends before.table after.table := by
  induction trace with
  | refl => exact extends_refl _
  | next earlier step ih =>
    apply extends_trans ih
    cases step with
    | reserve key => exact extends_refl _
    | install candidate issued => exact keepFirst_extends _ candidate.key candidate

/-- Issued candidates remain authorized after arbitrary intervening valid operations. -/
theorem steps_issued_extends [DecidableEq Key] {before after : State Key}
    (valid : Valid before) (trace : Steps before after) :
    Extends before.issued after.issued := by
  induction trace with
  | refl => exact extends_refl _
  | next earlier step ih =>
    apply extends_trans ih
    cases step with
    | reserve key => exact reserve_extends _ key (steps_valid valid earlier)
    | install candidate issued => exact extends_refl _

/-- Readback from any two completed interning calls agrees on the same key. -/
theorem concurrent_readback [DecidableEq Key] {before after : State Key} (trace : Steps before after)
    (first : before.table key = some left) (second : after.table key = some right) : left = right :=
  reads_agree (steps_table_extends trace) first second

/-- A family of shards, each containing a complete key map. -/
abbrev Shards (Shard Key Value : Type) := Shard → Table Key Value

/-- The effective lookup routes the key to its selected shard. -/
def flatten (choose : Key → Shard) (tables : Shards Shard Key Value) : Table Key Value :=
  fun key => tables (choose key) key

/-- Update only the selected shard. Key equality still distinguishes hash collisions. -/
def shardedInsert [DecidableEq Shard] [DecidableEq Key]
    (choose : Key → Shard) (tables : Shards Shard Key Value) (key : Key) (candidate : Value) :
    Shards Shard Key Value :=
  fun shard => if shard = choose key then keepFirst (tables shard) key candidate else tables shard

/-- Sharded insertion has exactly the same lookup semantics as one unsharded table. -/
theorem shardedInsert_correct [DecidableEq Shard] [DecidableEq Key]
    (choose : Key → Shard) (tables : Shards Shard Key Value) (key : Key) (candidate : Value) :
    flatten choose (shardedInsert choose tables key candidate) =
      keepFirst (flatten choose tables) key candidate := by
  funext other
  by_cases sameKey : other = key
  · subst other
    simp only [flatten, shardedInsert, ↓reduceIte, keepFirst]
    cases lookup : tables (choose key) key <;> simp_all [flatten, put]
  · by_cases sameShard : choose other = choose key
    · simp only [flatten, shardedInsert, sameShard, ↓reduceIte, keepFirst]
      cases lookup : tables (choose key) key <;> simp_all [flatten, put]
    · simp only [flatten, shardedInsert, sameShard, ↓reduceIte, keepFirst]
      cases lookup : tables (choose key) key <;> simp_all [flatten, put]

end MicroCFTA.Cache
