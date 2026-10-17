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

end

private def Lower (relation : Item → Item → Prop) (first : Item) (rest : List Item) : Prop :=
  ∀ item ∈ rest, relation first item

private theorem lower_cons {relation : Item → Item → Prop} {first next : Item} {rest : List Item}
    (head : relation first next) (tail : Lower relation first rest) : Lower relation first (next :: rest) := by
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail item member

private theorem lower_append {relation : Item → Item → Prop} {first : Item} {left right : List Item}
    (before : Lower relation first left) (after : Lower relation first right) :
    Lower relation first (left ++ right) := by
  intro item member
  exact (List.mem_append.mp member).elim (before item) (after item)

private theorem lower_trans (relation : Item → Item → Prop)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    {first next : Item} {rest : List Item} (before : relation first next)
    (after : Lower relation next rest) : Lower relation first rest :=
  fun item member => transitive before (after item member)

private theorem cons_count [DecidableEq Item] (relation : Item → Item → Prop) (head : Item) (tail inputs : List Item)
    (ordered : tail.Pairwise relation) (counts : ∀ item, tail.count item = inputs.count item)
    (lower : Lower relation head inputs) : (head :: tail).Pairwise relation := by
  classical
  exact List.pairwise_cons.mpr ⟨fun item member => lower item
    ((List.perm_iff_count.mpr counts).mem_iff.mp member), ordered⟩

private theorem merge_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (left right : List Item) (first : left.Pairwise relation) (last : right.Pairwise relation) :
    (merge gt left right).Pairwise relation := by
  classical
  cases left with
  | nil => simpa only [merge] using last
  | cons a left =>
      cases right with
      | nil => simpa only [merge] using first
      | cons b right =>
          obtain ⟨leftHead, leftOrdered⟩ := List.pairwise_cons.mp first
          obtain ⟨rightHead, rightOrdered⟩ := List.pairwise_cons.mp last
          rw [merge]
          split
          · rename_i take
            have before : relation b a := by simpa [take] using compared a b
            apply cons_count relation b (merge gt (a :: left) right) ((a :: left) ++ right)
              (merge_ordered relation gt transitive compared (a :: left) right first rightOrdered)
            · intro item; simp only [merge_count, List.count_append]
            · exact lower_append (lower_cons before (lower_trans relation transitive before leftHead)) rightHead
          · rename_i take
            have before : relation a b := by simpa [take] using compared a b
            apply cons_count relation a (merge gt left (b :: right)) (left ++ (b :: right))
              (merge_ordered relation gt transitive compared left (b :: right) leftOrdered last)
            · intro item; simp only [merge_count, List.count_append]
            · exact lower_append leftHead (lower_cons before (lower_trans relation transitive before rightHead))
termination_by left.length + right.length

private theorem merge3_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (left right third : List Item) (first : left.Pairwise relation) (middle : right.Pairwise relation)
    (last : third.Pairwise relation) : (merge3 gt left right third).Pairwise relation := by
  rw [merge3_nested]
  exact merge_ordered relation gt transitive compared _ _
    (merge_ordered relation gt transitive compared _ _ first middle) last

private theorem merge3X_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (held : Item) (left right third : List Item) (first : left.Pairwise relation)
    (middle : right.Pairwise relation) (last : third.Pairwise relation)
    (before : Lower relation held left) (after : Lower relation held right) :
    (merge3X gt held left right third).Pairwise relation := by
  classical
  rw [merge3X_nested]
  apply merge_ordered relation gt transitive compared _ _ _ last
  apply cons_count relation held (merge gt left right) (left ++ right)
    (merge_ordered relation gt transitive compared _ _ first middle)
  · intro item; simp only [merge_count, List.count_append]
  · exact lower_append before after

private theorem merge3Y_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (left : List Item) (held : Item) (right third : List Item) (first : left.Pairwise relation)
    (middle : right.Pairwise relation) (last : third.Pairwise relation)
    (before : Lower relation held right) (after : Lower relation held third) :
    (merge3Y gt left held right third).Pairwise relation := by
  classical
  cases left with
  | nil =>
      rw [merge3Y]
      apply cons_count relation held (merge gt right third) (right ++ third)
        (merge_ordered relation gt transitive compared _ _ middle last)
      · intro item; simp only [merge_count, List.count_append]
      · exact lower_append before after
  | cons a left =>
      obtain ⟨leftHead, leftOrdered⟩ := List.pairwise_cons.mp first
      rw [merge3Y]
      split
      · rename_i take
        have lower : relation held a := by simpa [take] using compared a held
        apply cons_count relation held (merge3 gt (a :: left) right third) (((a :: left) ++ right) ++ third)
          (merge3_ordered relation gt transitive compared _ _ _ first middle last)
        · intro item; simp only [merge3_count, List.count_append]
        · exact lower_append (lower_append (lower_cons lower (lower_trans relation transitive lower leftHead)) before) after
      · rename_i take
        have lower : relation a held := by simpa [take] using compared a held
        apply cons_count relation a (merge3Y gt left held right third) (((left ++ [held]) ++ right) ++ third)
          (merge3Y_ordered relation gt transitive compared _ _ _ _ leftOrdered middle last before after)
        · intro item; simp only [merge3Y_count, List.count_append]
        · exact lower_append (lower_append (lower_append leftHead (by simpa [Lower] using lower))
            (lower_trans relation transitive lower before)) (lower_trans relation transitive lower after)
termination_by left.length

mutual
private theorem merge4_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (left right third fourth : List Item) (first : left.Pairwise relation) (second : right.Pairwise relation)
    (thirdOrdered : third.Pairwise relation) (fourthOrdered : fourth.Pairwise relation) :
    (merge4 gt left right third fourth).Pairwise relation := by
  cases left with
  | nil => exact merge3_ordered relation gt transitive compared _ _ _ second thirdOrdered fourthOrdered
  | cons a left =>
      cases right with
      | nil => exact merge3_ordered relation gt transitive compared _ _ _ first thirdOrdered fourthOrdered
      | cons b right =>
          obtain ⟨leftHead, leftOrdered⟩ := List.pairwise_cons.mp first
          obtain ⟨rightHead, rightOrdered⟩ := List.pairwise_cons.mp second
          rw [merge4]
          split
          · rename_i take
            have before : relation b a := by simpa [take] using compared a b
            exact merge4X_ordered relation gt transitive compared b (a :: left) right third fourth
              first rightOrdered thirdOrdered fourthOrdered
              (lower_cons before (lower_trans relation transitive before leftHead)) rightHead
          · rename_i take
            have before : relation a b := by simpa [take] using compared a b
            exact merge4X_ordered relation gt transitive compared a left (b :: right) third fourth
              leftOrdered second thirdOrdered fourthOrdered leftHead
              (lower_cons before (lower_trans relation transitive before rightHead))
termination_by 4 * (left.length + right.length + third.length + fourth.length) + 3
decreasing_by all_goals simp_all only [List.length_cons]; omega

private theorem merge4X_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (held : Item) (left right third fourth : List Item) (first : left.Pairwise relation)
    (second : right.Pairwise relation) (thirdOrdered : third.Pairwise relation)
    (fourthOrdered : fourth.Pairwise relation) (before : Lower relation held left)
    (after : Lower relation held right) : (merge4X gt held left right third fourth).Pairwise relation := by
  cases third with
  | nil =>
      rw [merge4X]
      exact merge3X_ordered relation gt transitive compared _ _ _ _ first second fourthOrdered before after
  | cons c third =>
      cases fourth with
      | nil =>
          rw [merge4X]
          exact merge3X_ordered relation gt transitive compared _ _ _ _ first second thirdOrdered before after
      | cons d fourth =>
          obtain ⟨thirdHead, thirdTail⟩ := List.pairwise_cons.mp thirdOrdered
          obtain ⟨fourthHead, fourthTail⟩ := List.pairwise_cons.mp fourthOrdered
          rw [merge4X]
          split
          · rename_i take
            have lower : relation d c := by simpa [take] using compared c d
            exact merge4XY_ordered relation gt transitive compared held left right d (c :: third) fourth
              first second thirdOrdered fourthTail before after
              (lower_cons lower (lower_trans relation transitive lower thirdHead)) fourthHead
          · rename_i take
            have lower : relation c d := by simpa [take] using compared c d
            exact merge4XY_ordered relation gt transitive compared held left right c third (d :: fourth)
              first second thirdTail fourthOrdered before after thirdHead
              (lower_cons lower (lower_trans relation transitive lower fourthHead))
termination_by 4 * (1 + left.length + right.length + third.length + fourth.length) + 2
decreasing_by all_goals simp_all only [List.length_cons]; omega

private theorem merge4Y_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (left right : List Item) (held : Item) (third fourth : List Item) (first : left.Pairwise relation)
    (second : right.Pairwise relation) (thirdOrdered : third.Pairwise relation)
    (fourthOrdered : fourth.Pairwise relation) (before : Lower relation held third)
    (after : Lower relation held fourth) : (merge4Y gt left right held third fourth).Pairwise relation := by
  cases right with
  | nil =>
      rw [merge4Y]
      exact merge3Y_ordered relation gt transitive compared _ _ _ _ first thirdOrdered fourthOrdered before after
  | cons b right =>
      cases left with
      | nil =>
          rw [merge4Y]
          exact merge3Y_ordered relation gt transitive compared _ _ _ _ second thirdOrdered fourthOrdered before after
      | cons a left =>
          obtain ⟨leftHead, leftOrdered⟩ := List.pairwise_cons.mp first
          obtain ⟨rightHead, rightOrdered⟩ := List.pairwise_cons.mp second
          rw [merge4Y]
          split
          · rename_i take
            have lower : relation b a := by simpa [take] using compared a b
            exact merge4XY_ordered relation gt transitive compared b (a :: left) right held third fourth
              first rightOrdered thirdOrdered fourthOrdered
              (lower_cons lower (lower_trans relation transitive lower leftHead)) rightHead before after
          · rename_i take
            have lower : relation a b := by simpa [take] using compared a b
            exact merge4XY_ordered relation gt transitive compared a left (b :: right) held third fourth
              leftOrdered second thirdOrdered fourthOrdered leftHead
              (lower_cons lower (lower_trans relation transitive lower rightHead)) before after
termination_by 4 * (left.length + right.length + 1 + third.length + fourth.length) + 2

private theorem merge4XY_ordered (relation : Item → Item → Prop) (gt : Item → Item → Bool)
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    (compared : ∀ a b, if gt a b then relation b a else relation a b)
    (held : Item) (left right : List Item) (other : Item) (third fourth : List Item)
    (first : left.Pairwise relation) (second : right.Pairwise relation)
    (thirdOrdered : third.Pairwise relation) (fourthOrdered : fourth.Pairwise relation)
    (leftLower : Lower relation held left) (rightLower : Lower relation held right)
    (thirdLower : Lower relation other third) (fourthLower : Lower relation other fourth) :
    (merge4XY gt held left right other third fourth).Pairwise relation := by
  classical
  rw [merge4XY]
  split
  · rename_i take
    have lower : relation other held := by simpa [take] using compared held other
    apply cons_count relation other (merge4X gt held left right third fourth)
      ((([held] ++ left) ++ right) ++ third ++ fourth)
      (merge4X_ordered relation gt transitive compared _ _ _ _ _ first second thirdOrdered fourthOrdered leftLower rightLower)
    · intro item; simp only [merge4X_count, List.count_append]
    · exact lower_append (lower_append (lower_append
        (lower_append (by simpa [Lower] using lower) (lower_trans relation transitive lower leftLower))
        (lower_trans relation transitive lower rightLower)) thirdLower) fourthLower
  · rename_i take
    have lower : relation held other := by simpa [take] using compared held other
    apply cons_count relation held (merge4Y gt left right other third fourth)
      (((left ++ right) ++ [other]) ++ third ++ fourth)
      (merge4Y_ordered relation gt transitive compared _ _ _ _ _ first second thirdOrdered fourthOrdered thirdLower fourthLower)
    · intro item; simp only [merge4Y_count, List.count_append]
    · exact lower_append (lower_append (lower_append (lower_append leftLower rightLower)
        (by simpa [Lower] using lower)) (lower_trans relation transitive lower thirdLower))
        (lower_trans relation transitive lower fourthLower)
termination_by 4 * (1 + left.length + right.length + 1 + third.length + fourth.length) + 0
end

end MicroCFTA.SourceListSortOrdered
