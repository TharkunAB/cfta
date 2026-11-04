import Init.Data.List.Range
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas

import MicroCFTA.SourceRecursiveIntersectionDescriptorCarrier

namespace MicroCFTA.SourceRecursiveIntersectionDomain

theorem originalDescriptorCarrier_length_bound {Symbol Guard : Type}
    (state : MicroCFTA.InternedConstructorTemplates.State Symbol Guard) :
    (originalDescriptorCarrier state).length ≤
        2 ^ (state.nodes.next +
          (MicroCFTA.SourceRecursiveIntersectionInputView.inventory state).length ^ 2) ∧
      2 ^ (state.nodes.next +
          (MicroCFTA.SourceRecursiveIntersectionInputView.inventory state).length ^ 2) ≤
        2 ^ (state.nodes.next + (1 + 4 * state.nodes.next) ^ 2)
 := by
  have successor_conversion (n : Nat) : n + 1 = Nat.succ n := by
    calc
      n + 1 = Nat.succ (n + 0) := Nat.add_succ n 0
      _ = Nat.succ n := by rw [Nat.add_comm n 0, Nat.zero_add]
  let inputs := MicroCFTA.SourceRecursiveIntersectionInputView.inventory state
  let pairs := inputs.flatMap fun left =>
    inputs.map fun right => MicroCFTA.IntersectSchedule.pair left right
  let empty : MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey := ⟨[], []⟩
  let anchor := MicroCFTA.IntersectSchedule.pair
    MicroCFTA.IntersectSchedule.Input.empty MicroCFTA.IntersectSchedule.Input.empty
  let pairChoices := List.foldr
    (fun pair keys => keys ++ keys.map (fun key => extend key [] pair))
    [empty] pairs
  have inventory_tail_length (names : List Nat) :
      (names.flatMap fun name =>
        [MicroCFTA.IntersectSchedule.Input.node name,
         MicroCFTA.IntersectSchedule.Input.mu name,
         MicroCFTA.IntersectSchedule.Input.union name,
         MicroCFTA.IntersectSchedule.Input.ref name]).length = 4 * names.length := by
    induction names with
    | nil =>
        simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero]
    | cons name rest ih =>
        rw [List.flatMap_cons, List.length_append, ih]
        simp only [List.length_cons, List.length_nil]
        change 4 + 4 * rest.length = 4 * (rest.length + 1)
        rw [successor_conversion rest.length, Nat.mul_succ]
        exact Nat.add_comm _ _
  have inventory_length : inputs.length = 1 + 4 * state.nodes.next := by
    change (MicroCFTA.IntersectSchedule.Input.empty ::
      (List.range state.nodes.next).flatMap fun name =>
        [MicroCFTA.IntersectSchedule.Input.node name,
         MicroCFTA.IntersectSchedule.Input.mu name,
         MicroCFTA.IntersectSchedule.Input.union name,
         MicroCFTA.IntersectSchedule.Input.ref name]).length = 1 + 4 * state.nodes.next
    rw [List.length_cons, inventory_tail_length, List.length_range]
    exact Nat.add_comm _ _
  have image_length (outer : List MicroCFTA.IntersectSchedule.Input) :
      (outer.flatMap fun left =>
        inputs.map fun right => MicroCFTA.IntersectSchedule.pair left right).length =
          inputs.length * outer.length := by
    induction outer with
    | nil =>
        simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero]
    | cons left rest ih =>
        rw [List.flatMap_cons, List.length_append, List.length_map, ih,
          List.length_cons, successor_conversion rest.length, Nat.mul_succ]
        exact Nat.add_comm _ _
  have pairs_length : pairs.length = inputs.length ^ 2 := by
    calc
      pairs.length = inputs.length * inputs.length := image_length inputs
      _ = inputs.length ^ 2 := (Nat.pow_two inputs.length).symm
  have pair_choices_length (pool : List (Nat × Nat)) :
      (List.foldr
        (fun pair keys => keys ++ keys.map (fun key => extend key [] pair))
        [empty] pool).length = 2 ^ pool.length := by
    induction pool with
    | nil =>
        simp only [List.foldr_nil, List.length_cons, List.length_nil,
          Nat.zero_add, Nat.pow_zero]
    | cons pair rest ih =>
        rw [List.foldr_cons, List.length_append, List.length_map, ih,
          List.length_cons, successor_conversion rest.length, Nat.pow_succ, Nat.mul_two]
  have name_choices_length (names : List Nat) :
      ∀ (seed : List MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey) (k : Nat),
        seed.length = 2 ^ k →
        (List.foldr
          (fun name keys => keys ++ keys.map (fun key =>
            MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey.mk
              (extend key [name] anchor).free key.seen))
          seed names).length = 2 ^ (names.length + k) := by
    induction names with
    | nil =>
        intro seed k seed_length
        simp only [List.foldr_nil, List.length_nil, Nat.zero_add]
        exact seed_length
    | cons name rest ih =>
        intro seed k seed_length
        rw [List.foldr_cons, List.length_append, List.length_map,
          ih seed k seed_length, List.length_cons]
        have exponent : (rest.length + 1) + k = Nat.succ (rest.length + k) := by
          rw [successor_conversion rest.length, Nat.add_comm (Nat.succ rest.length) k,
            Nat.add_succ, Nat.add_comm k rest.length]
        rw [exponent, Nat.pow_succ, Nat.mul_two]
  have carrier_length : (originalDescriptorCarrier state).length =
      2 ^ (state.nodes.next + pairs.length) := by
    change (List.foldr
      (fun name keys => keys ++ keys.map (fun key =>
        MicroCFTA.IntersectionFlatMemoKeyDomain.DomainKey.mk
          (extend key [name] anchor).free key.seen))
      pairChoices (List.range state.nodes.next)).length =
        2 ^ (state.nodes.next + pairs.length)
    have counted := name_choices_length (List.range state.nodes.next)
      pairChoices pairs.length (pair_choices_length pairs)
    rw [List.length_range] at counted
    exact counted
  constructor
  · rw [carrier_length, pairs_length]
    exact Nat.le_refl _
  · change 2 ^ (state.nodes.next + inputs.length ^ 2) ≤
      2 ^ (state.nodes.next + (1 + 4 * state.nodes.next) ^ 2)
    rw [inventory_length]
    exact Nat.le_refl _

end MicroCFTA.SourceRecursiveIntersectionDomain
