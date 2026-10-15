import MicroCFTA.SourceListSortRuns

/-!
# Exact finite sortBy schedule for the installed source toolchain

This is the base 4.22 natural-run sorter, including its short-list cases and
special five-run and six-run reductions. All counts are exact for arbitrary
comparators. The added empty merge-loop case is unreachable from actualSort.
-/
namespace MicroCFTA.SourceListSort

/-- Reduce source runs with the exact three-way and four-way schedule. -/
def reduceOnce (gt : Item → Item → Bool) : List (List Item) → List (List Item)
  | [] => []
  | [a] => [a]
  | [a, b] => [merge gt a b]
  | [a, b, c] => [merge3 gt a b c]
  | [a, b, c, d, e] => [merge gt a b, merge3 gt c d e]
  | [a, b, c, d, e, f] => [merge3 gt a b c, merge3 gt d e f]
  | a :: b :: c :: d :: rest => merge4 gt a b c d :: reduceOnce gt rest

/-- Each source reduction strictly decreases the number of runs when at least two remain. -/
theorem reduceOnce_shorter (gt : Item → Item → Bool) (runs : List (List Item)) (multiple : 2 ≤ runs.length) :
    (reduceOnce gt runs).length < runs.length := by
  match runs with
  | [] | [_] => simp at multiple
  | [a, b] | [a, b, c] | [a, b, c, d] | [a, b, c, d, e] | [a, b, c, d, e, f] => simp [reduceOnce]
  | a :: b :: c :: d :: e :: f :: g :: rest =>
      rw [reduceOnce] <;> try simp
      have smaller := reduceOnce_shorter gt (e :: f :: g :: rest) (by simp)
      simp only [List.length_cons] at smaller ⊢
      omega
termination_by runs.length

/-- Run reduction preserves each original occurrence count. -/
theorem reduceOnce_count [DecidableEq Item] (gt : Item → Item → Bool) (runs : List (List Item)) (item : Item) :
    (reduceOnce gt runs).flatten.count item = runs.flatten.count item := by
  match runs with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] =>
      simp [reduceOnce, merge_count, merge3_count, merge4_count, List.count_append, Nat.add_assoc]
  | a :: b :: c :: d :: e :: f :: g :: rest =>
      rw [reduceOnce] <;> try simp
      simp only [merge4_count]
      rw [reduceOnce_count gt (e :: f :: g :: rest) item]
      simp only [List.flatten_cons, List.count_append]
      omega
termination_by runs.length

/-- Merge all source runs; actualSort never supplies the totalized empty case. -/
def mergeAll (gt : Item → Item → Bool) (runs : List (List Item)) : List Item :=
  match runs with
  | [] => []
  | [run] => run
  | first :: second :: rest => mergeAll gt (reduceOnce gt (first :: second :: rest))
termination_by runs.length
decreasing_by exact reduceOnce_shorter _ _ (by simp)

/-- The complete finite source merge loop preserves all occurrence counts. -/
theorem mergeAll_count [DecidableEq Item] (gt : Item → Item → Bool) (runs : List (List Item)) (item : Item) :
    (mergeAll gt runs).count item = runs.flatten.count item := by
  match runs with
  | [] => simp [mergeAll]
  | [run] => simp [mergeAll]
  | first :: second :: rest =>
      rw [mergeAll, mergeAll_count gt (reduceOnce gt (first :: second :: rest)) item, reduceOnce_count]
termination_by runs.length
decreasing_by exact reduceOnce_shorter _ _ (by simp)

/-- Execute the installed source sort's short-list branches and complete natural-run schedule. -/
def actualSort (gt : Item → Item → Bool) : List Item → List Item
  | [] => []
  | [a] => [a]
  | [a, b] => merge gt [a] [b]
  | [a, b, c] => merge3 gt [a] [b] [c]
  | [a, b, c, d] => merge4 gt [a] [b] [c] [d]
  | input => mergeAll gt (sequences gt input)

/-- The installed source sortBy tests only whether its comparison returns greater. -/
def sortBy (compare : Item → Item → Ordering) : List Item → List Item :=
  actualSort (fun left right => compare left right == .gt)

/-- The exact source sorter preserves every original occurrence, with no comparator-law premise. -/
theorem actualSort_count [DecidableEq Item] (gt : Item → Item → Bool) (input : List Item) (item : Item) :
    (actualSort gt input).count item = input.count item := by
  match input with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] =>
      simp [actualSort, merge_count, merge3_count, merge4_count, List.count_cons, Nat.add_comm, Nat.add_left_comm]
  | _ :: _ :: _ :: _ :: _ :: _ =>
      rw [actualSort, mergeAll_count, sequences_count] <;> simp

/-- Finite source sortBy returns an exact permutation even for a nontransitive raw comparator. -/
theorem sortBy_perm (compare : Item → Item → Ordering) (input : List Item) : (sortBy compare input).Perm input := by
  classical
  apply List.perm_iff_count.mpr
  exact fun item => actualSort_count _ input item

/-- The physical source order contains exactly the original class occurrences. -/
theorem sortBy_mem (compare : Item → Item → Ordering) (input : List Item) (item : Item) :
    item ∈ sortBy compare input ↔ item ∈ input := (sortBy_perm compare input).mem_iff

end MicroCFTA.SourceListSort
