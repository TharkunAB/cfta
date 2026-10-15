import MicroCFTA.EnumerationCorrectness
import MicroCFTA.Cache

/-!
# Current finite-map enumeration slots

The effective map uses the existing typed lookup and insertion primitives.
Allocated keys form an exact nonnegative prefix. Initialization, fresh
insertion, and in-range raw writes derive correspondence with the earlier
list slots. Eliminated values remain stored. Representative reads retain
the actual bounded union-find result. This module does not model IntMap
tree storage, strict evaluation, machine overflow, or the whole scheduler.
-/
namespace MicroCFTA.SourceCurrentEnumerationStorage

/-- Only the fresh supply and value slots belong to this storage adapter. -/
structure State (Value : Type) where
  next : Nat
  values : Cache.Table Int Value

/-- Read the earlier list at a nonnegative key; negative keys are absent. -/
def listLookup (values : List Value) : Int → Option Value
  | .ofNat index => values[index]?
  | .negSucc _ => none

/-- The map has exactly the list slots and the same next fresh index. -/
structure Corresponds (state : State Value) (values : List Value) : Prop where
  aligned : state.next = values.length
  lookup : ∀ key, state.values key = listLookup values key

/-- The source initial map has only UVar zero. -/
def initial (root : Value) : State Value := ⟨1, Cache.put (fun _ => none) 0 root⟩

/-- Read the raw supplied UVar without resolving its representative. -/
def read (state : State Value) (index : Nat) : Option Value := state.values (Int.ofNat index)

/-- Source insertion writes the raw address even when that key was absent. -/
def write (state : State Value) (index : Nat) (value : Value) : State Value :=
  {state with values := Cache.put state.values (Int.ofNat index) value}

/-- Fresh allocation inserts at the current supply and advances it once. -/
def allocate (state : State Value) (value : Value) : Nat × State Value :=
  (state.next, ⟨state.next + 1, Cache.put state.values (Int.ofNat state.next) value⟩)

/-- Initial source insertion derives the complete root-list correspondence. -/
theorem initial_corresponds (root : Value) : Corresponds (initial root) [root] := by
  refine ⟨rfl, ?_⟩
  intro key
  cases key with
  | ofNat index => cases index <;> rfl
  | negSucc index => rfl

/-- Every raw read returns exactly its earlier list slot. -/
theorem Corresponds.read_eq {state : State Value} {values : List Value} (same : Corresponds state values) (index : Nat) :
    read state index = values[index]? := same.lookup _

/-- Every negative machine-key abstraction is absent in a corresponding map. -/
theorem Corresponds.negative {state : State Value} {values : List Value} (same : Corresponds state values) (index : Nat) :
    state.values (.negSucc index) = none := same.lookup _

private theorem listLookup_set (values : List Value) (index : Nat) (value : Value) (inside : index < values.length) :
    listLookup (values.set index value) = Cache.put (listLookup values) (Int.ofNat index) value := by
  funext key
  cases key with
  | ofNat other =>
      by_cases equal : index = other
      · subst other
        simp only [listLookup, Cache.put, List.getElem?_set, ↓reduceIte, inside]
      · have different : Int.ofNat other ≠ Int.ofNat index := fun h => equal (Int.ofNat.inj h).symm
        simp only [listLookup, Cache.put, List.getElem?_set, ite_eq_right equal, ite_eq_right different]
  | negSucc other => rfl

/-- Map insertion agrees with list update only at an allocated address. -/
theorem Corresponds.write_corresponds {state : State Value} {values : List Value} (same : Corresponds state values)
    (index : Nat) (value : Value) (inside : index < state.next) :
    Corresponds (write state index value) (values.set index value) := by
  have bounded : index < values.length := by simpa only [same.aligned] using inside
  have table : state.values = listLookup values := funext same.lookup
  refine ⟨by simp only [write, List.length_set, same.aligned], ?_⟩
  intro key
  simp only [write, table, listLookup_set values index value bounded]

private theorem listLookup_append (values : List Value) (value : Value) :
    listLookup (values ++ [value]) = Cache.put (listLookup values) (Int.ofNat values.length) value := by
  funext key
  cases key with
  | negSucc index => rfl
  | ofNat index =>
      by_cases inside : index < values.length
      · have different : Int.ofNat index ≠ Int.ofNat values.length := by intro h; have := Int.ofNat.inj h; omega
        simp only [listLookup, Cache.put, List.getElem?_append, ite_eq_left inside, ite_eq_right different]
      · by_cases equal : index = values.length
        · subst index
          simp [listLookup, Cache.put]
        · have different : Int.ofNat index ≠ Int.ofNat values.length := fun h => equal (Int.ofNat.inj h)
          have tail : ([value] : List Value)[index - values.length]? = none :=
            List.getElem?_eq_none (by simp only [List.length_singleton]; omega)
          simp only [listLookup, List.getElem?_append, ite_eq_right inside, tail, Cache.put, ite_eq_right different,
            List.getElem?_eq_none (by omega : values.length ≤ index)]

/-- Fresh insertion derives append correspondence and preserves every earlier list slot. -/
theorem Corresponds.allocate_corresponds {state : State Value} {values : List Value} (same : Corresponds state values) (value : Value) :
    (allocate state value).1 = values.length ∧ Corresponds (allocate state value).2 (values ++ [value]) := by
  have table : state.values = listLookup values := funext same.lookup
  refine ⟨same.aligned, ?_, ?_⟩
  · simp only [allocate, List.length_append, List.length_singleton, same.aligned]
  · intro key
    simp only [allocate, table, same.aligned, listLookup_append]

/-- Present slots have exactly the allocated natural addresses. -/
theorem Corresponds.domain {state : State Value} {values : List Value} (same : Corresponds state values) (index : Nat) :
    (∃ value, read state index = some value) ↔ index < state.next := by
  rw [same.read_eq, same.aligned]
  constructor
  · rintro ⟨value, found⟩
    exact (List.getElem?_eq_some_iff.mp found).1
  · intro inside
    exact ⟨values[index], List.getElem?_eq_getElem inside⟩

/-- A finite prefix contains every present signed key. -/
theorem Corresponds.finite_keys {state : State Value} {values : List Value} (same : Corresponds state values)
    (key : Int) (value : Value) (found : state.values key = some value) :
    ∃ index ∈ List.range state.next, key = Int.ofNat index := by
  cases key with
  | negSucc index => rw [same.negative] at found; cases found
  | ofNat index => exact ⟨index, List.mem_range.mpr ((same.domain index).mp ⟨value, found⟩), rfl⟩

/-- A source storage history allows only fresh insertions and allocated raw writes. -/
inductive History (root : Value) : State Value → Prop where
  | initial : History root (initial root)
  | fresh (prior : History root state) : History root (allocate state value).2
  | write (prior : History root state) (inside : index < state.next) : History root (write state index value)

/-- The allocated-prefix invariant is derived from the initial map and each reached storage action. -/
theorem History.corresponds {root : Value} {state : State Value} (history : History root state) :
    ∃ values, Corresponds state values := by
  induction history with
  | initial => exact ⟨_, initial_corresponds _⟩
  | fresh prior ih =>
      obtain ⟨values, same⟩ := ih
      exact ⟨_, (same.allocate_corresponds _).2⟩
  | write prior inside ih =>
      obtain ⟨values, same⟩ := ih
      exact ⟨_, same.write_corresponds _ _ inside⟩

/-- Every reached storage history derives its exact allocated prefix. -/
theorem History.domain {root : Value} {state : State Value} (history : History root state) (index : Nat) :
    (∃ value, read state index = some value) ↔ index < state.next := by
  obtain ⟨values, same⟩ := history.corresponds
  exact same.domain index

/-- Eliminating an allocated UVar keeps its slot and its exact list correspondence. -/
theorem eliminated_slot {state : State (EnumerationState.UVarValue Symbol)} {values}
    (same : Corresponds state values) (index : Nat) (inside : index < state.next) :
    Corresponds (write state index .eliminated) (values.set index .eliminated) ∧
      read (write state index .eliminated) index = some .eliminated := by
  exact ⟨same.write_corresponds index .eliminated inside, by simp [read, write, Cache.put]⟩

/-- The current root map has the same payload and supply as the existing initialized model. -/
theorem initial_model (root : Nat) :
    (initial (EnumerationState.UVarValue.unenumerated (Symbol := Symbol) (some root) [])).next =
      (EnumerationState.initial root : EnumerationState.State Symbol Guard).counter ∧
    Corresponds (initial (.unenumerated (some root) []))
      (EnumerationState.initial root : EnumerationState.State Symbol Guard).values :=
  ⟨rfl, initial_corresponds _⟩

/-- Actual aligned model allocation agrees with the new fresh-key map insertion. -/
theorem allocate_model (before : EnumerationState.State Symbol Guard)
    (state : State (EnumerationState.UVarValue Symbol)) (same : Corresponds state before.values)
    (aligned : EnumerationCorrectness.SupplyAligned before) (node : Option Nat) :
    (allocate state (.unenumerated node [])).1 = before.counter ∧
      Corresponds (allocate state (.unenumerated node [])).2 (EnumerationState.allocated node before).values := by
  exact ⟨same.aligned.trans aligned.symm, (same.allocate_corresponds _).2⟩

/-- An allocated old-model raw write agrees with current insertion at the same supplied address. -/
theorem write_model (before : EnumerationState.State Symbol Guard)
    (state : State (EnumerationState.UVarValue Symbol)) (same : Corresponds state before.values)
    (aligned : EnumerationCorrectness.SupplyAligned before) (index : Nat) (value : EnumerationState.UVarValue Symbol)
    (inside : index < before.counter) :
    Corresponds (write state index value) ({before with values := before.values.set index value}).values := by
  exact same.write_corresponds index value (by rw [same.aligned, ← aligned]; exact inside)

/-- Resolve the actual bounded representative before reading the unchanged slot map. -/
def getValue (fuel : Nat) (forest : UnionFind.Forest) (index : Nat) (state : State Value) :
    Option (Value × UnionFind.Forest) := do
  let found ← UnionFind.findRoot fuel forest index
  let value ← read state found.representative
  pure (value, found.forest)

/-- Allocated bounded union-find reads derive a present representative slot and the same compressed forest. -/
theorem representative_read {state : State Value} {values : List Value} (same : Corresponds state values)
    (fuel : Nat) (forest : UnionFind.Forest) (index : Nat)
    (bounded : EnumerationCorrectness.ForestBound state.next forest) (inside : index < state.next)
    (found : UnionFind.Result) (done : UnionFind.findRoot fuel forest index = some found) :
    ∃ value, values[found.representative]? = some value ∧ read state found.representative = some value ∧
      getValue fuel forest index state = some (value, found.forest) := by
  have allocated := (EnumerationCorrectness.findRoot_bounded fuel forest state.next index bounded inside found done).1
  obtain ⟨value, stored⟩ := (same.domain found.representative).mpr allocated
  exact ⟨value, (same.read_eq _).symm.trans stored, stored, by simp [getValue, done, stored]⟩

/-- An absent-key insertion differs from an out-of-range list update. -/
theorem unallocated_boundary (value : Value) :
    (Cache.put (fun _ : Int => none) 0 value) 0 = some value ∧
      listLookup (([] : List Value).set 0 value) 0 = none := by
  exact ⟨by simp [Cache.put], rfl⟩

end MicroCFTA.SourceCurrentEnumerationStorage
