import MicroCFTA.EnumerationStateIndexValidity

namespace MicroCFTA.EnumerationStateValueAccess

open EnumerationState EnumerationStateReferenceBounds EnumerationStateIndexValidity

variable {Symbol Guard α β : Type}

local instance : Monad List where
  pure := fun value => [value]
  bind := fun branches next => List.flatMap next branches

private theorem mem_bind (first : EnumerateM Symbol Guard α)
    (next : α → EnumerateM Symbol Guard β) (before : EnumerationState.State Symbol Guard)
    (value : β) (after : EnumerationState.State Symbol Guard) :
    Except.ok (value, after) ∈ ExceptT.run ((first >>= next) before) ↔
      ∃ result middle, Except.ok (result, middle) ∈ ExceptT.run (first before) ∧
        Except.ok (value, after) ∈ ExceptT.run (next result middle) := by
  dsimp [Bind.bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run]
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨item, member, run⟩
    cases item with
    | error error => simp [ExceptT.bindCont, Pure.pure] at run
    | ok pair => exact ⟨pair.1, pair.2, member, run⟩
  · rintro ⟨result, middle, member, run⟩
    exact ⟨Except.ok (result, middle), member, run⟩

private theorem lookup_exists (values : List α) (key : Nat) (below : key < values.length) :
    ∃ value, values[key]? = some value := by
  induction values generalizing key with
  | nil => simp at below
  | cons first rest ih =>
    cases key with
    | zero => exact ⟨first, rfl⟩
    | succ key =>
      obtain ⟨value, found⟩ := ih key (by simpa using below)
      exact ⟨value, by simpa using found⟩

private theorem lookup_is_member (values : List α) (key : Nat) (value : α)
    (found : values[key]? = some value) : value ∈ values := by
  induction values generalizing key with
  | nil => simp at found
  | cons first rest ih => cases key <;> simp_all <;> grind

/-- Every allocated variable has an actual stored value and the read preserves the state. -/
theorem rawValue_defined (state : EnumerationState.State Symbol Guard) (key : Nat)
    (indexed : Indexed state) (below : key < state.counter) :
    ∃ value, Except.ok (value, state) ∈ ExceptT.run (EnumerationState.rawValue key state) ∧
      ValueBelow state.counter value := by
  obtain ⟨value, found⟩ := lookup_exists state.values key (by simpa [indexed.shape] using below)
  refine ⟨value, ?_, indexed.values value (lookup_is_member _ _ _ found)⟩
  unfold EnumerationState.rawValue
  apply (mem_bind _ _ _ _ _).mpr
  refine ⟨state, state, ?_, ?_⟩
  · change Except.ok (state, state) ∈ [Except.ok (state, state)]
    exact List.mem_singleton_self _
  · rw [found]
    change Except.ok _ ∈ [Except.ok _]
    exact List.mem_singleton_self _

/-- Resolving and reading an allocated variable succeeds at the computed current-counter fuel. -/
theorem getValue_computed_fuel (state : EnumerationState.State Symbol Guard) (key : Nat)
    (indexed : Indexed state) (below : key < state.counter) :
    ∃ value after, Except.ok (value, after) ∈ ExceptT.run
      (EnumerationState.getValue (state.counter + 1) key state) ∧
      Indexed after ∧ ValueBelow after.counter value ∧ after.counter = state.counter := by
  obtain ⟨root, middle, resolved⟩ :=
    representative_computed_fuel state state.counter key indexed.supported indexed.total
  obtain ⟨preserved, rootBelow, counter⟩ :=
    representative_preserves_references (state.counter + 1) key below state root middle indexed resolved
  have indexedMiddle : Indexed middle := by
    simpa only [Indexed, ← counter] using preserved
  obtain ⟨value, accessed, valueBelow⟩ :=
    rawValue_defined middle root indexedMiddle (by omega)
  refine ⟨value, middle, ?_, indexedMiddle, valueBelow, counter.symm⟩
  unfold EnumerationState.getValue
  exact (mem_bind _ _ _ _ _).mpr ⟨root, middle, resolved, accessed⟩

/-- Initial node expansion needs no supplied invariant to obtain defined later value reads. -/
theorem initial_node_getValue (graph : Graph Symbol Guard) (fuel root : Nat)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateNode graph fuel [] root (EnumerationState.initial root)))
    (key : Nat) (below : key < after.counter) :
    ∃ value finalState, Except.ok (value, finalState) ∈ ExceptT.run
      (EnumerationState.getValue (after.counter + 1) key after) ∧
      Indexed finalState ∧ ValueBelow finalState.counter value ∧ finalState.counter = after.counter := by
  obtain ⟨indexed, _, _⟩ := enumerateNode_initial_indices graph fuel root fragment after returned
  exact getValue_computed_fuel after key indexed below

/-- Initial edge expansion needs no supplied invariant to obtain defined later value reads. -/
theorem initial_edge_getValue (graph : Graph Symbol Guard) (fuel root : Nat)
    (edge : Edge Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateEdge graph fuel [] edge (EnumerationState.initial root)))
    (key : Nat) (below : key < after.counter) :
    ∃ value finalState, Except.ok (value, finalState) ∈ ExceptT.run
      (EnumerationState.getValue (after.counter + 1) key after) ∧
      Indexed finalState ∧ ValueBelow finalState.counter value ∧ finalState.counter = after.counter := by
  obtain ⟨indexed, _, _⟩ := enumerateEdge_initial_indices graph fuel root edge fragment after returned
  exact getValue_computed_fuel after key indexed below

end MicroCFTA.EnumerationStateValueAccess
