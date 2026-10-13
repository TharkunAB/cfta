import MicroCFTA.EqualityRawLeafInventory
import MicroCFTA.MergedRowGroups

/-!
# Merged peer targets in the finite raw-leaf carrier

At a nullary symbol, the source retains up to four original rows. A larger
group becomes one Top row. This preserves the existing finite carrier.
The old physical target worker does not perform this step. These results do
not silently extend that worker's complete-record correspondence.
-/
namespace MicroCFTA.MergedRawLeaves
open SourceGuards FullSyntax EqualityRawLeafInventory

/-- The unconstrained row already belongs to every source-generated finite inventory. -/
def top (initial : List (Guard Formula)) : Row initial :=
  ⟨⟨.top, by simp [GuardConjunction.atoms]⟩, Or.inr (by simp [GuardConjunction.normalize, GuardConjunction.canonical,
    GuardConjunction.atoms, GuardConjunction.conjoin]), by
    simp [EqualityRawLeafConstruction.accepted, SourceCompactGuards.sourceEqualities,
      EqualityLeafProjectionAdmittedSource.fitsLeaf, SourceCompactGuards.positiveNormalized]⟩

noncomputable local instance : DecidableEq (Row initial) := by classical exact inferInstance

/-- Enumerate the distinct selected complete rows at one nullary symbol. -/
noncomputable def selected (leaf : Leaf initial symbols) (symbol : Fin symbols) : List (Row initial) := by
  classical
  exact ((inventory initial).filter (fun row => decide (leaf symbol row))).eraseDups

/-- The generated list contains precisely the original selected rows. -/
theorem selected_member (leaf : Leaf initial symbols) (symbol : Fin symbols) (row : Row initial) :
    row ∈ selected leaf symbol ↔ leaf symbol row := by
  simp [selected, inventory_complete row]

/-- Counting selected rows counts complete distinct source keys. -/
theorem selected_distinct (leaf : Leaf initial symbols) (symbol : Fin symbols) :
    (selected leaf symbol).Nodup := MergedRowGroups.eraseDups_nodup _

/-- The current nullary source merge uses the literal four-edge threshold. -/
noncomputable def merge (leaf : Leaf initial symbols) : Leaf initial symbols := fun symbol row =>
  row ∈ MergedRowGroups.squash (top initial) (selected leaf symbol)

/-- The current source either retains each small-group row or returns Top for a larger group. -/
theorem merge_cases (leaf : Leaf initial symbols) (symbol : Fin symbols) (row : Row initial) :
    merge leaf symbol row ↔
      (leaf symbol row ∧ (selected leaf symbol).length ≤ 4) ∨
      (row = top initial ∧ 4 < (selected leaf symbol).length) := by
  rw [merge, MergedRowGroups.squash_member, selected_member]

/-- A source symbol survives exactly when it had an original row. -/
theorem support (leaf : Leaf initial symbols) (symbol : Fin symbols) :
    (∃ row, merge leaf symbol row) ↔ ∃ row, leaf symbol row := by
  constructor
  · rintro ⟨row, member⟩
    rcases (merge_cases leaf symbol row).mp member with ⟨present, _⟩ | ⟨_, large⟩
    · exact ⟨row, present⟩
    · cases found : selected leaf symbol with
      | nil => simp [found] at large
      | cons first rest => exact ⟨first, (selected_member leaf symbol first).mp (by simp [found])⟩
  · rintro ⟨row, present⟩
    by_cases small : (selected leaf symbol).length ≤ 4
    · exact ⟨row, (merge_cases leaf symbol row).mpr (Or.inl ⟨present, small⟩)⟩
    · exact ⟨top initial, (merge_cases leaf symbol (top initial)).mpr (Or.inr ⟨rfl, by omega⟩)⟩

/-- A group of at most four raw rows preserves every complete row. -/
theorem small_exact (leaf : Leaf initial symbols) (symbol : Fin symbols)
    (small : (selected leaf symbol).length ≤ 4) (row : Row initial) :
    merge leaf symbol row ↔ leaf symbol row := by
  simp [merge, MergedRowGroups.squash_small _ _ small, selected_member]

/-- A leaf with at most four complete rows per symbol needs no merge. -/
theorem unchanged (leaf : Leaf initial symbols)
    (small : ∀ symbol, (selected leaf symbol).length ≤ 4) : merge leaf = leaf := by
  funext symbol row
  exact propext (small_exact leaf symbol (small symbol) row)

/-- The selected output inventory is the exact source group up to row order. -/
theorem selected_merge_perm (leaf : Leaf initial symbols) (symbol : Fin symbols) :
    (selected (merge leaf) symbol).Perm (MergedRowGroups.squash (top initial) (selected leaf symbol)) := by
  have distinct : (MergedRowGroups.squash (top initial) (selected leaf symbol)).Nodup := by
    unfold MergedRowGroups.squash
    split
    · exact selected_distinct leaf symbol
    · simp
  apply (List.perm_ext_iff_of_nodup (selected_distinct (merge leaf) symbol) distinct).mpr
  intro row
  exact selected_member (merge leaf) symbol row

/-- Every merged nullary symbol has at most four distinct complete rows. -/
theorem merged_bound (leaf : Leaf initial symbols) (symbol : Fin symbols) :
    (selected (merge leaf) symbol).length ≤ 4 := by
  rw [(selected_merge_perm leaf symbol).length_eq]
  exact MergedRowGroups.squash_bound _ _

/-- Merging the same finite raw leaf twice has no further effect. -/
theorem idempotent (leaf : Leaf initial symbols) : merge (merge leaf) = merge leaf :=
  unchanged (merge leaf) (merged_bound leaf)

/-- The source group can add accepted terms but cannot remove one. -/
theorem covers (leaf : Leaf initial symbols) (symbol : Fin symbols)
    (holds : Row initial → Prop) (topHolds : holds (top initial))
    (accepted : ∃ row, leaf symbol row ∧ holds row) :
    ∃ row, merge leaf symbol row ∧ holds row := by
  obtain ⟨row, present, accepted⟩ := accepted
  by_cases small : (selected leaf symbol).length ≤ 4
  · exact ⟨row, (merge_cases leaf symbol row).mpr (Or.inl ⟨present, small⟩), accepted⟩
  · exact ⟨top initial, (merge_cases leaf symbol (top initial)).mpr (Or.inr ⟨rfl, by omega⟩), topHolds⟩

/-- Each target-first intersection still has the derived finite source progress measure. -/
theorem merged_target_progress (target before : Leaf initial symbols) :
    EqualityLeafProjectionSyntax.Progress rank (intersect (merge target) before) before :=
  leaf_progress (merge target) before

end MicroCFTA.MergedRawLeaves
