import MicroCFTA.EnumerationStateIndexValidity
import MicroCFTA.EnumerationStateValueAccess

set_option maxHeartbeats 2000000

namespace MicroCFTA.EnumerationStateWorkerIndexValidity

open EnumerationState EnumerationStateReferenceBounds EnumerationStateIndexValidity

variable {Symbol Guard α β : Type}

local instance : Monad List where
  pure := fun value => [value]
  bind := fun branches next => List.flatMap next branches

private theorem fragment_mono (held : FragmentBelow lower fragment) (larger : lower ≤ upper) :
    FragmentBelow upper fragment := by
  induction held with
  | hole key below => exact .hole key (Nat.lt_of_lt_of_le below larger)
  | node symbol children below ih => exact .node symbol children (fun child member => ih child member)

private theorem suspensions_mono (held : SuspensionsBelow lower scs) (larger : lower ≤ upper) :
    SuspensionsBelow upper scs := by
  intro entry member
  exact Nat.lt_of_lt_of_le (held entry member) larger

private theorem value_mono (held : ValueBelow lower value) (larger : lower ≤ upper) :
    ValueBelow upper value := by
  cases value with
  | unenumerated node scs => exact suspensions_mono held larger
  | enumerated fragment => exact fragment_mono held larger
  | eliminated => trivial

private def Safe (lower : Nat) (post : Nat → α → Prop)
    (action : EnumerateM Symbol Guard α) : Prop :=
  ∀ before value after, Indexed before → lower ≤ before.counter →
    Except.ok (value, after) ∈ ExceptT.run (action before) →
    Indexed after ∧ post after.counter value ∧ before.counter ≤ after.counter

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
    exact ⟨.ok (result, middle), member, run⟩

private theorem safe_raise (held : Safe lower post action) (larger : lower ≤ upper) :
    Safe upper post action := by
  intro before value after state lowerBound run
  exact held before value after state (Nat.le_trans larger lowerBound) run

private theorem pure_safe (held : ∀ upper, lower ≤ upper → post upper value) :
    Safe lower post (pure value : EnumerateM Symbol Guard α) := by
  intro before result after state lowerBound run
  change Except.ok (result, after) ∈ [Except.ok (value, before)] at run
  have paired := Except.ok.inj (List.mem_singleton.mp run)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj paired
  exact ⟨state, held _ lowerBound, Nat.le_refl _⟩

private theorem bind_safe (first : Safe lower pre action)
    (next : ∀ value cap, lower ≤ cap → pre cap value → Safe cap post (following value)) :
    Safe lower post (action >>= following) := by
  intro before value after state lowerBound run
  obtain ⟨result, middle, firstRun, nextRun⟩ := (mem_bind _ _ _ _ _).mp run
  obtain ⟨middleState, firstValue, firstMono⟩ := first before result middle state lowerBound firstRun
  obtain ⟨afterState, resultValue, nextMono⟩ :=
    next result middle.counter (Nat.le_trans lowerBound firstMono) firstValue
      middle value after middleState (Nat.le_refl _) nextRun
  exact ⟨afterState, resultValue, Nat.le_trans firstMono nextMono⟩

private theorem failure_safe (error : EnumerationState.Error) :
    Safe lower post (EnumerationState.failure error : EnumerateM Symbol Guard α) := by
  intro before value after state lowerBound run
  change Except.ok (value, after) ∈ [Except.error error] at run
  simp at run

private theorem reject_safe :
    Safe lower post (EnumerationState.reject : EnumerateM Symbol Guard α) := by
  intro before value after state lowerBound run
  change Except.ok (value, after) ∈ [] at run
  simp at run

private theorem require_safe (condition : Bool) :
    Safe lower (fun _ _ => True) (EnumerationState.require condition : EnumerateM Symbol Guard Unit) := by
  cases condition with
  | false => exact reject_safe
  | true => exact pure_safe (fun _ _ => trivial)

private theorem modify_safe (update : EnumerationState.State Symbol Guard → EnumerationState.State Symbol Guard)
    (preserves : ∀ state, Indexed state → lower ≤ state.counter → Indexed (update state))
    (counter : ∀ state, (update state).counter = state.counter) :
    Safe lower (fun _ _ => True) (modify update : EnumerateM Symbol Guard Unit) := by
  intro before value after state lowerBound run
  change Except.ok (value, after) ∈ [Except.ok ((), update before)] at run
  have paired := Except.ok.inj (List.mem_singleton.mp run)
  have equal := congrArg Prod.snd paired
  dsimp only at equal
  subst after
  exact ⟨preserves before state lowerBound, trivial, by rw [counter]; omega⟩

private theorem get_bind_safe
    (next : EnumerationState.State Symbol Guard → EnumerateM Symbol Guard α)
    (held : ∀ before value after, Indexed before → lower ≤ before.counter →
      Except.ok (value, after) ∈ ExceptT.run (next before before) →
      Indexed after ∧ post after.counter value ∧ before.counter ≤ after.counter) :
    Safe lower post ((get : EnumerateM Symbol Guard (EnumerationState.State Symbol Guard)) >>= next) := by
  intro before value after state lowerBound run
  obtain ⟨snapshot, middle, got, continued⟩ := (mem_bind _ _ _ _ _).mp run
  change Except.ok (snapshot, middle) ∈ [Except.ok (before, before)] at got
  have paired := Except.ok.inj (List.mem_singleton.mp got)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj paired
  exact held _ value after state lowerBound continued

private theorem representative_safe (fuel key : Nat) (below : key < lower) :
    Safe lower (fun cap result => result < cap)
      (EnumerationState.representative fuel key : EnumerateM Symbol Guard Nat) := by
  intro before value after state lowerBound run
  obtain ⟨preserved, result, counter⟩ :=
    EnumerationStateReferenceBounds.representative_preserves_references fuel key
      (Nat.lt_of_lt_of_le below lowerBound) before value after state run
  exact ⟨by simpa only [Indexed, ← counter] using preserved, by omega, by omega⟩

private theorem set_preserves_all (predicate : α → Prop) (values : List α) (index : Nat)
    (replacement : α) (held : ∀ value ∈ values, predicate value) (fresh : predicate replacement) :
    ∀ value ∈ values.set index replacement, predicate value := by
  induction values generalizing index with
  | nil => simp
  | cons first rest ih => cases index <;> simp_all [List.set] <;> grind

private theorem lookup_is_member (values : List α) (index : Nat) (value : α)
    (lookup : values[index]? = some value) : value ∈ values := by
  induction values generalizing index with
  | nil => simp at lookup
  | cons first rest ih => cases index <;> simp_all <;> grind

private theorem setValue_safe (key : Nat) (value : UVarValue Symbol) (held : ValueBelow lower value) :
    Safe lower (fun _ _ => True) (EnumerationState.setValue key value : EnumerateM Symbol Guard Unit) := by
  unfold EnumerationState.setValue
  apply modify_safe
  · intro before state lowerBound
    refine ⟨state.counter, ?_, state.supported, state.parents, state.total, ?_, state.obligations⟩
    · simpa using state.shape
    · exact set_preserves_all _ _ _ _ state.values (value_mono held lowerBound)
  · intro state
    rfl

private theorem rawValue_safe (key : Nat) :
    Safe lower (fun cap value => ValueBelow cap value)
      (EnumerationState.rawValue key : EnumerateM Symbol Guard (UVarValue Symbol)) := by
  unfold EnumerationState.rawValue
  apply get_bind_safe
  intro before value after state lowerBound run
  cases looked : before.values[key]? with
  | none =>
      simp only [looked] at run
      exact failure_safe _ before value after state lowerBound run
  | some cell =>
      simp only [looked] at run
      exact pure_safe (lower := before.counter)
        (fun cap increase => value_mono (state.values cell (lookup_is_member _ _ _ looked)) increase)
        before value after state (Nat.le_refl _) run

private theorem getValue_safe (fuel key : Nat) (below : key < lower) :
    Safe lower (fun cap value => ValueBelow cap value)
      (EnumerationState.getValue fuel key : EnumerateM Symbol Guard (UVarValue Symbol)) := by
  unfold EnumerationState.getValue
  apply bind_safe (representative_safe fuel key below)
  intro root cap larger rootBelow
  exact rawValue_safe root

private theorem get_then_safe
    (next : EnumerationState.State Symbol Guard → EnumerateM Symbol Guard α)
    (held : ∀ snapshot, Safe lower post (next snapshot)) :
    Safe lower post ((get : EnumerateM Symbol Guard (EnumerationState.State Symbol Guard)) >>= next) := by
  apply get_bind_safe
  intro before value after state lowerBound run
  exact held before before value after state lowerBound run

private theorem node_safe (graph : Graph Symbol Guard) (fuel node : Nat)
    (scs : List Suspended) (references : SuspensionsBelow lower scs) :
    Safe lower (fun cap fragment => FragmentBelow cap fragment)
      (EnumerationState.enumerateNode graph fuel scs node) := by
  intro before fragment after state lowerBound run
  exact enumerateNode_preserves_indices graph fuel node scs before fragment after state
    (suspensions_mono references lowerBound) run

private theorem out_safe (graph : Graph Symbol Guard) (fuel key : Nat) (below : key < lower) :
    Safe lower (fun cap fragment => FragmentBelow cap fragment)
      (EnumerationState.enumerateOut graph fuel key) := by
  unfold EnumerationState.enumerateOut
  apply bind_safe (getValue_safe (fuel + 1) key below)
  intro value valueCap growValue valueBelow
  cases value with
  | eliminated => exact reject_safe
  | enumerated fragment => exact reject_safe
  | unenumerated node scs =>
      cases node with
      | none => exact reject_safe
      | some node =>
          have references : SuspensionsBelow valueCap scs := valueBelow
          apply bind_safe (safe_raise (representative_safe (fuel + 1) key below) growValue)
          intro root rootCap growRoot rootBelow
          apply get_then_safe
          intro snapshot
          dsimp only
          apply bind_safe
          · apply modify_safe
            · intro state indexed lowerBound
              exact ⟨indexed.counter, indexed.shape, indexed.supported, indexed.parents,
                indexed.total, indexed.values, indexed.obligations⟩
            · intro state
              rfl
          · intro _ preparedCap growPrepared _
            apply bind_safe (node_safe graph fuel _ scs (suspensions_mono references (by omega)))
            intro fragment expandedCap growExpanded fragmentBelow
            apply bind_safe
            · apply modify_safe
              · intro state indexed lowerBound
                exact ⟨indexed.counter, indexed.shape, indexed.supported, indexed.parents,
                  indexed.total, indexed.values, indexed.obligations⟩
              · intro state
                rfl
            · intro _ restoredCap growRestored _
              apply bind_safe (setValue_safe root (.enumerated fragment)
                (fragment_mono fragmentBelow growRestored))
              intro _ storedCap growStored _
              exact pure_safe (fun cap larger => fragment_mono fragmentBelow (by omega))

/-- A successful actual worker step preserves current value indices. -/
theorem enumerateOut_preserves_indices (graph : Graph Symbol Guard) (fuel key : Nat)
    (before : EnumerationState.State Symbol Guard) (fragment : Fragments.Fragment Symbol)
    (after : EnumerationState.State Symbol Guard) (indexed : Indexed before)
    (below : key < before.counter)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateOut graph fuel key before)) :
    Indexed after ∧ FragmentBelow after.counter fragment ∧ before.counter ≤ after.counter := by
  exact out_safe graph fuel key below before fragment after indexed (Nat.le_refl _) returned

/-- The initial actual worker step needs no supplied invariant or index bound. -/
theorem enumerateOut_initial_indices (graph : Graph Symbol Guard) (fuel root : Nat)
    (fragment : Fragments.Fragment Symbol) (after : EnumerationState.State Symbol Guard)
    (returned : Except.ok (fragment, after) ∈ ExceptT.run
      (EnumerationState.enumerateOut graph fuel 0 (EnumerationState.initial root))) :
    Indexed after ∧ FragmentBelow after.counter fragment ∧ 1 ≤ after.counter := by
  exact enumerateOut_preserves_indices graph fuel 0 (EnumerationState.initial root) fragment after
    (initial_invariant root) (by change 0 < 1; omega) returned

/-- An initial node expansion and a later root step preserve both returned fragments. -/
theorem initial_node_then_out_indices (graph : Graph Symbol Guard) (nodeFuel outFuel root : Nat)
    (first last : Fragments.Fragment Symbol)
    (middle after : EnumerationState.State Symbol Guard)
    (expanded : Except.ok (first, middle) ∈ ExceptT.run
      (EnumerationState.enumerateNode graph nodeFuel [] root (EnumerationState.initial root)))
    (returned : Except.ok (last, after) ∈ ExceptT.run
      (EnumerationState.enumerateOut graph outFuel 0 middle)) :
    Indexed after ∧ FragmentBelow after.counter first ∧ FragmentBelow after.counter last ∧
      1 ≤ after.counter := by
  obtain ⟨indexed, firstBelow, positive⟩ := enumerateNode_initial_indices graph nodeFuel root first middle expanded
  obtain ⟨finalIndexed, lastBelow, monotone⟩ :=
    enumerateOut_preserves_indices graph outFuel 0 middle last after indexed (by omega) returned
  exact ⟨finalIndexed, fragment_mono firstBelow monotone, lastBelow, by omega⟩

/-- An initial edge expansion and a later root step preserve both returned fragments. -/
theorem initial_edge_then_out_indices (graph : Graph Symbol Guard) (edgeFuel outFuel root : Nat)
    (edge : Edge Symbol Guard) (first last : Fragments.Fragment Symbol)
    (middle after : EnumerationState.State Symbol Guard)
    (expanded : Except.ok (first, middle) ∈ ExceptT.run
      (EnumerationState.enumerateEdge graph edgeFuel [] edge (EnumerationState.initial root)))
    (returned : Except.ok (last, after) ∈ ExceptT.run
      (EnumerationState.enumerateOut graph outFuel 0 middle)) :
    Indexed after ∧ FragmentBelow after.counter first ∧ FragmentBelow after.counter last ∧
      1 ≤ after.counter := by
  obtain ⟨indexed, firstBelow, positive⟩ := enumerateEdge_initial_indices graph edgeFuel root edge first middle expanded
  obtain ⟨finalIndexed, lastBelow, monotone⟩ :=
    enumerateOut_preserves_indices graph outFuel 0 middle last after indexed (by omega) returned
  exact ⟨finalIndexed, fragment_mono firstBelow monotone, lastBelow, by omega⟩

end MicroCFTA.EnumerationStateWorkerIndexValidity
