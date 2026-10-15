import MicroCFTA.SourceEqualityNeededMap
import MicroCFTA.TermOperations

/-!
# Ordered child-list adjustments in requireAll

The source folds ascending IntMap entries from the right. Each entry adjusts
one signed list position. Negative and missing positions leave the list
unchanged. These proofs concern returned lists. They do not impose a native
lazy evaluation schedule on the constructor callbacks.
-/
namespace MicroCFTA.SourceEqualityNeededAdjust
open SourceEqualityNeededMap

/-- Adjust one signed source child position. -/
def adjust (index : Int) (change : α → α) (values : List α) : List α :=
  if index < 0 then values else TermOperations.adjustList change index.toNat values

/-- The natural-index worker has exactly the source split-and-rebuild equation. -/
theorem adjustList_split (index : Nat) (change : α → α) (values : List α) :
    TermOperations.adjustList change index values =
      let (initial, remaining) := values.splitAt index
      match remaining with
      | [] => values
      | value :: rest => initial ++ change value :: rest := by
  induction index generalizing values with
  | zero => cases values <;> simp [TermOperations.adjustList]
  | succ index ih =>
      cases values with
      | nil => simp [TermOperations.adjustList]
      | cons value rest =>
          simp only [TermOperations.adjustList, List.splitAt_eq, List.take_succ_cons, List.drop_succ_cons]
          rw [ih]
          simp only [List.splitAt_eq]
          cases rest.drop index <;> rfl

/-- Every signed adjustment preserves the source child count. -/
theorem adjust_length (index : Int) (change : α → α) (values : List α) :
    (adjust index change values).length = values.length := by
  unfold adjust
  split
  · rfl
  · exact TermOperations.adjustList_length change index.toNat values

/-- Exactly the selected nonnegative position observes the callback. -/
theorem adjust_lookup (index : Int) (query : Nat) (change : α → α) (values : List α) :
    (adjust index change values)[query]? =
      if (query : Int) = index then (values[query]?).map change else values[query]? := by
  unfold adjust
  split
  next negative => rw [ite_eq_right (by omega)]
  next nonnegative =>
    rw [TermOperations.adjustList_lookup]
    by_cases same : (query : Int) = index
    · have natural : query = index.toNat := by omega
      rw [ite_eq_left natural, ite_eq_left same]
    · have natural : query ≠ index.toNat := by omega
      rw [ite_eq_right natural, ite_eq_right same]

/-- The source IntMap fold keeps its ascending entry order and right-fold structure. -/
def apply (change : β → α → α) (entries : List (Int × β)) (values : List α) : List α :=
  entries.foldr (fun entry result => adjust entry.1 (change entry.2) result) values

/-- No child adjustment adds or removes a position. -/
theorem apply_length (change : β → α → α) (entries : List (Int × β)) (values : List α) :
    (apply change entries values).length = values.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simpa only [apply, List.foldr_cons, adjust_length] using ih

/-- Ascending unique keys apply one callback to the original value at each selected position. -/
theorem apply_lookup (change : β → α → α) (entries : List (Int × β)) (ordered : Ascending entries)
    (values : List α) (query : Nat) :
    (apply change entries values)[query]? =
      match lookup (query : Int) entries with
      | none => values[query]?
      | some selected => (values[query]?).map (change selected) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨index, selected⟩ := entry
      have order := List.pairwise_cons.mp ordered
      change (adjust index (change selected) (apply change rest values))[query]? = _
      rw [adjust_lookup, ih order.2]
      by_cases same : (query : Int) = index
      · have missing : lookup (query : Int) rest = none := by
          apply lookup_none
          intro key child member
          have larger := order.1 (key, child) member
          dsimp at larger
          omega
        rw [ite_eq_left same, missing]
        simp only [lookup, ite_eq_left same]
      · simp only [same, ite_false, lookup]

/-- A missing source child cannot cause its callback to run or create a new slot. -/
theorem apply_missing (change : β → α → α) (entries : List (Int × β)) (ordered : Ascending entries)
    (values : List α) (query : Nat) (missing : values[query]? = none) :
    (apply change entries values)[query]? = none := by
  rw [apply_lookup change entries ordered values query]
  cases lookup (query : Int) entries <;> simp [missing]

/-- A selected existing position receives exactly its own stored child requirement. -/
theorem apply_selected (change : β → α → α) (entries : List (Int × β)) (ordered : Ascending entries)
    (values : List α) (query : Nat) (selected : β) (member : ((query : Int), selected) ∈ entries) :
    (apply change entries values)[query]? = (values[query]?).map (change selected) := by
  rw [apply_lookup change entries ordered values query, lookup_of_mem _ _ _ ordered member]

/-- Negative and high source keys retain the original finite child list. -/
theorem missing_key_example :
    apply (fun amount value : Nat => amount + value) [(-1, 100), (9, 200)] [1, 2] = [1, 2] := by rfl

end MicroCFTA.SourceEqualityNeededAdjust
