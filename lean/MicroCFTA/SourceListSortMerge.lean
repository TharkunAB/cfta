import Std

/-!
# The installed base 4.22 sortBy merge workers

The source is GHC 9.14.1's GHC.Internal.Data.OldList.actualSort. The workers
retain its fused three-way and four-way branches. No comparator law is used.
-/
namespace MicroCFTA.SourceListSort

/-- Merge two runs, taking the left head unless the source comparator returns greater. -/
def merge (gt : Item → Item → Bool) : List Item → List Item → List Item
  | [], right => right
  | left, [] => left
  | a :: left, b :: right =>
      if gt a b then b :: merge gt (a :: left) right else a :: merge gt left (b :: right)
termination_by left right => left.length + right.length

mutual
/-- Select the first head of the source fused three-way merge. -/
def merge3 (gt : Item → Item → Bool) (left right third : List Item) : List Item :=
  match left, right with
  | [], right => merge gt right third
  | left, [] => merge gt left third
  | a :: left, b :: right =>
      if gt a b then merge3X gt b (a :: left) right third else merge3X gt a left (b :: right) third
termination_by 4 * (left.length + right.length + third.length) + 1
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- Compare a held first-pair head with the third run. -/
def merge3X (gt : Item → Item → Bool) (held : Item) (left right third : List Item) : List Item :=
  match third with
  | [] => held :: merge gt left right
  | c :: third =>
      if gt held c then c :: merge3X gt held left right third else held :: merge3 gt left right (c :: third)
termination_by 4 * (1 + left.length + right.length + third.length) + 0

/-- Compare the first run with a held head of the remaining pair. -/
def merge3Y (gt : Item → Item → Bool) (left : List Item) (held : Item) (right third : List Item) : List Item :=
  match left with
  | [] => held :: merge gt right third
  | a :: left =>
      if gt a held then held :: merge3 gt (a :: left) right third else a :: merge3Y gt left held right third
termination_by 4 * (left.length + 1 + right.length + third.length) + 1

/-- Select the first head of the source fused four-way merge. -/
def merge4 (gt : Item → Item → Bool) (left right third fourth : List Item) : List Item :=
  match left, right with
  | [], right => merge3 gt right third fourth
  | left, [] => merge3 gt left third fourth
  | a :: left, b :: right =>
      if gt a b then merge4X gt b (a :: left) right third fourth else merge4X gt a left (b :: right) third fourth

/-- Select a head from the last pair while the first pair has a held head. -/
def merge4X (gt : Item → Item → Bool) (held : Item) (left right third fourth : List Item) : List Item :=
  match third, fourth with
  | [], fourth => merge3X gt held left right fourth
  | third, [] => merge3X gt held left right third
  | c :: third, d :: fourth =>
      if gt c d then merge4XY gt held left right d (c :: third) fourth else merge4XY gt held left right c third (d :: fourth)
termination_by 4 * (1 + left.length + right.length + third.length + fourth.length) + 2
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- Select a head from the first pair while the last pair has a held head. -/
def merge4Y (gt : Item → Item → Bool) (left right : List Item) (held : Item) (third fourth : List Item) : List Item :=
  match left, right with
  | left, [] => merge3Y gt left held third fourth
  | [], right => merge3Y gt right held third fourth
  | a :: left, b :: right =>
      if gt a b then merge4XY gt b (a :: left) right held third fourth else merge4XY gt a left (b :: right) held third fourth
termination_by 4 * (left.length + right.length + 1 + third.length + fourth.length) + 2

/-- Compare the held heads of both source run pairs. -/
def merge4XY (gt : Item → Item → Bool) (first : Item) (left right : List Item)
    (second : Item) (third fourth : List Item) : List Item :=
  if gt first second then second :: merge4X gt first left right third fourth
  else first :: merge4Y gt left right second third fourth
termination_by 4 * (1 + left.length + right.length + 1 + third.length + fourth.length) + 0
end

/-- Two-way merging preserves the count of every original occurrence. -/
theorem merge_count [DecidableEq Item] (gt : Item → Item → Bool) (left right : List Item) (item : Item) :
    (merge gt left right).count item = left.count item + right.count item := by
  cases left with
  | nil => simp [merge]
  | cons a left =>
      cases right with
      | nil => simp [merge]
      | cons b right =>
          rw [merge]
          split
          · rw [List.count_cons, merge_count gt (a :: left) right item]
            simp only [List.count_cons]
            omega
          · rw [List.count_cons, merge_count gt left (b :: right) item]
            simp only [List.count_cons]
            omega
termination_by left.length + right.length

mutual
/-- The three-way source merge preserves all occurrence counts. -/
theorem merge3_count [DecidableEq Item] (gt : Item → Item → Bool) (left right third : List Item) (item : Item) :
    (merge3 gt left right third).count item = left.count item + right.count item + third.count item := by
  cases left with
  | nil => simp [merge3, merge_count]
  | cons a left =>
      cases right with
      | nil => simp [merge3, merge_count]
      | cons b right =>
          rw [merge3]
          split
          · rw [merge3X_count gt b (a :: left) right third item]
            simp only [List.count_cons, List.count_nil]
            omega
          · rw [merge3X_count gt a left (b :: right) third item]
            simp only [List.count_cons, List.count_nil]
            omega
termination_by 4 * (left.length + right.length + third.length) + 1
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- A held first-pair head contributes one occurrence to the three-way count. -/
theorem merge3X_count [DecidableEq Item] (gt : Item → Item → Bool) (held : Item) (left right third : List Item) (item : Item) :
    (merge3X gt held left right third).count item = [held].count item + left.count item + right.count item + third.count item := by
  cases third with
  | nil => simp only [merge3X, List.count_cons, merge_count, List.count_nil]; omega
  | cons c third =>
      rw [merge3X]
      split
      · rw [List.count_cons, merge3X_count gt held left right third item]
        simp only [List.count_cons]
        omega
      · rw [List.count_cons, merge3_count gt left right (c :: third) item]
        simp only [List.count_cons, List.count_nil]
        omega
termination_by 4 * (1 + left.length + right.length + third.length) + 0

/-- A held second-pair head contributes one occurrence to the three-way count. -/
theorem merge3Y_count [DecidableEq Item] (gt : Item → Item → Bool) (left : List Item) (held : Item) (right third : List Item) (item : Item) :
    (merge3Y gt left held right third).count item = left.count item + [held].count item + right.count item + third.count item := by
  cases left with
  | nil => simp only [merge3Y, List.count_cons, merge_count, List.count_nil]; omega
  | cons a left =>
      rw [merge3Y]
      split
      · rw [List.count_cons, merge3_count gt (a :: left) right third item]
        simp only [List.count_cons, List.count_nil]
        omega
      · rw [List.count_cons, merge3Y_count gt left held right third item]
        simp only [List.count_cons]
        omega
termination_by 4 * (left.length + 1 + right.length + third.length) + 1

/-- The four-way source merge preserves all occurrence counts. -/
theorem merge4_count [DecidableEq Item] (gt : Item → Item → Bool) (left right third fourth : List Item) (item : Item) :
    (merge4 gt left right third fourth).count item = left.count item + right.count item + third.count item + fourth.count item := by
  cases left with
  | nil => simp [merge4, merge3_count]
  | cons a left =>
      cases right with
      | nil => simp [merge4, merge3_count]
      | cons b right =>
          rw [merge4]
          split
          · rw [merge4X_count gt b (a :: left) right third fourth item]
            simp only [List.count_cons, List.count_nil]
            omega
          · rw [merge4X_count gt a left (b :: right) third fourth item]
            simp only [List.count_cons, List.count_nil]
            omega

/-- A held first-pair head contributes one occurrence to the four-way count. -/
theorem merge4X_count [DecidableEq Item] (gt : Item → Item → Bool) (held : Item) (left right third fourth : List Item) (item : Item) :
    (merge4X gt held left right third fourth).count item =
      [held].count item + left.count item + right.count item + third.count item + fourth.count item := by
  cases third with
  | nil => simp [merge4X, merge3X_count]
  | cons c third =>
      cases fourth with
      | nil => simp [merge4X, merge3X_count]
      | cons d fourth =>
          rw [merge4X]
          split
          · rw [merge4XY_count gt held left right d (c :: third) fourth item]
            simp only [List.count_cons, List.count_nil]
            omega
          · rw [merge4XY_count gt held left right c third (d :: fourth) item]
            simp only [List.count_cons, List.count_nil]
            omega
termination_by 4 * (1 + left.length + right.length + third.length + fourth.length) + 2
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- A held last-pair head contributes one occurrence to the four-way count. -/
theorem merge4Y_count [DecidableEq Item] (gt : Item → Item → Bool) (left right : List Item) (held : Item) (third fourth : List Item) (item : Item) :
    (merge4Y gt left right held third fourth).count item =
      left.count item + right.count item + [held].count item + third.count item + fourth.count item := by
  cases right with
  | nil => simp [merge4Y, merge3Y_count]
  | cons b right =>
      cases left with
      | nil => simp [merge4Y, merge3Y_count]
      | cons a left =>
          rw [merge4Y]
          split
          · rw [merge4XY_count gt b (a :: left) right held third fourth item]
            simp only [List.count_cons, List.count_nil]
            omega
          · rw [merge4XY_count gt a left (b :: right) held third fourth item]
            simp only [List.count_cons, List.count_nil]
            omega
termination_by 4 * (left.length + right.length + 1 + third.length + fourth.length) + 2

/-- Both held pair heads are retained exactly once by the source merge. -/
theorem merge4XY_count [DecidableEq Item] (gt : Item → Item → Bool) (first : Item) (left right : List Item)
    (second : Item) (third fourth : List Item) (item : Item) :
    (merge4XY gt first left right second third fourth).count item =
      [first].count item + left.count item + right.count item + [second].count item + third.count item + fourth.count item := by
  rw [merge4XY]
  split
  · rw [List.count_cons, merge4X_count gt first left right third fourth item]
    simp only [List.count_cons, List.count_nil]
    omega
  · rw [List.count_cons, merge4Y_count gt left right second third fourth item]
    simp only [List.count_cons, List.count_nil]
    omega
termination_by 4 * (1 + left.length + right.length + 1 + third.length + fourth.length) + 0
end

end MicroCFTA.SourceListSort
