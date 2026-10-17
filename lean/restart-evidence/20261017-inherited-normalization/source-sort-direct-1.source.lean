import MicroCFTA.SourceListSort
import MicroCFTA.SourceEqualityClassOrder

/-!
# Ordered output of the actual source sort

The fused merge workers equal nested two-way merges. Natural run detection
supplies ordered runs. A total transitive comparison therefore orders the
complete source result, including its short-list and special run cases.
-/
namespace MicroCFTA.SourceListSortOrdered
open SourceListSort

private theorem merge_permutation (gt : Item → Item → Bool) (left right : List Item) :
    (merge gt left right).Perm (left ++ right) := by
  classical
  apply List.perm_iff_count.mpr
  intro item
  simp only [merge_count, List.count_append]

mutual
private theorem merge3_nested (gt : Item → Item → Bool) (left right third : List Item) :
    merge3 gt left right third = merge gt (merge gt left right) third := by
  cases left with
  | nil => simp [merge3, merge]
  | cons a left =>
      cases right with
      | nil => simp [merge3, merge]
      | cons b right =>
          rw [merge3]
          split
          · rw [merge3X_nested, merge]
            simp_all
          · rw [merge3X_nested, merge]
            simp_all
termination_by 4 * (left.length + right.length + third.length) + 1
decreasing_by all_goals simp_all only [List.length_cons]; omega

private theorem merge3X_nested (gt : Item → Item → Bool) (held : Item) (left right third : List Item) :
    merge3X gt held left right third = merge gt (held :: merge gt left right) third := by
  cases third with
  | nil => simp [merge3X, merge]
  | cons c third =>
      rw [merge3X, merge]
      split
      · rw [merge3X_nested]
      · rw [merge3_nested]
termination_by 4 * (1 + left.length + right.length + third.length) + 0

private theorem merge3Y_nested (gt : Item → Item → Bool) (left : List Item) (held : Item) (right third : List Item) :
    merge3Y gt left held right third = merge gt left (held :: merge gt right third) := by
  cases left with
  | nil => simp [merge3Y, merge]
  | cons a left =>
      rw [merge3Y, merge]
      split
      · rw [merge3_nested]
      · rw [merge3Y_nested]
termination_by 4 * (left.length + 1 + right.length + third.length) + 1

private theorem merge4_nested (gt : Item → Item → Bool) (left right third fourth : List Item) :
    merge4 gt left right third fourth = merge gt (merge gt left right) (merge gt third fourth) := by
  cases left with
  | nil => simp [merge4, merge3_nested, merge]
  | cons a left =>
      cases right with
      | nil => simp [merge4, merge3_nested, merge]
      | cons b right =>
          rw [merge4]
          split
          · rw [merge4X_nested, merge]
            simp_all
          · rw [merge4X_nested, merge]
            simp_all
termination_by 4 * (left.length + right.length + third.length + fourth.length) + 3
decreasing_by all_goals simp_all only [List.length_cons]; omega

private theorem merge4X_nested (gt : Item → Item → Bool) (held : Item) (left right third fourth : List Item) :
    merge4X gt held left right third fourth = merge gt (held :: merge gt left right) (merge gt third fourth) := by
  cases third with
  | nil => simp [merge4X, merge3X_nested, merge]
  | cons c third =>
      cases fourth with
      | nil => simp [merge4X, merge3X_nested, merge]
      | cons d fourth =>
          rw [merge4X]
          split
          · rw [merge4XY_nested]
            conv => rhs; rw [merge]
            simp_all
          · rw [merge4XY_nested]
            conv => rhs; rw [merge]
            simp_all
termination_by 4 * (1 + left.length + right.length + third.length + fourth.length) + 2
decreasing_by all_goals simp_all only [List.length_cons]; omega

private theorem merge4Y_nested (gt : Item → Item → Bool) (left right : List Item) (held : Item) (third fourth : List Item) :
    merge4Y gt left right held third fourth = merge gt (merge gt left right) (held :: merge gt third fourth) := by
  cases right with
  | nil => simp [merge4Y, merge3Y_nested, merge]
  | cons b right =>
      cases left with
      | nil => simp [merge4Y, merge3Y_nested, merge]
      | cons a left =>
          rw [merge4Y]
          split
          · rw [merge4XY_nested]
            conv => rhs; rw [merge]
            simp_all
          · rw [merge4XY_nested]
            conv => rhs; rw [merge]
            simp_all
termination_by 4 * (left.length + right.length + 1 + third.length + fourth.length) + 2

private theorem merge4XY_nested (gt : Item → Item → Bool) (first : Item) (left right : List Item)
    (second : Item) (third fourth : List Item) :
    merge4XY gt first left right second third fourth =
      merge gt (first :: merge gt left right) (second :: merge gt third fourth) := by
  rw [merge4XY, merge]
  split
  · rw [merge4X_nested]
  · rw [merge4Y_nested]
termination_by 4 * (1 + left.length + right.length + 1 + third.length + fourth.length) + 0
end

end MicroCFTA.SourceListSortOrdered
