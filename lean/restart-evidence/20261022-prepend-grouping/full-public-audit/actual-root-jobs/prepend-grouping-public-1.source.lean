import MicroCFTA.SourceCurrentMergeGrouping

namespace MicroCFTA.SourceCurrentPrependGrouping
open SourceCurrentMergeGrouping (Table Iteration)
variable {Key Item : Type}

/-- Combine the new list before the old optional bucket. -/
def insertWith [DecidableEq Key] (table : Table Key Item)
    (entry : Key × List Item) : Table Key Item :=
  fun query => if query = entry.1 then some (entry.2 ++ (table query).getD []) else table query

/-- Insert source rows as singleton lists from an empty table. -/
def fromRows [DecidableEq Key] (key : Item → Key) (rows : List Item) : Table Key Item :=
  rows.foldl (fun table row => insertWith table (key row, [row])) (fun _ => none)

/-- Reverse every stored bucket and retain absent keys. -/
def reverseTable (table : Table Key Item) : Table Key Item :=
  fun query => (table query).map List.reverse

/-- The singleton schedule equals the mapped source pair fold. -/
theorem pair_fold [DecidableEq Key] (key : Item → Key) (rows : List Item) :
    (rows.map (fun row => (key row, [row]))).foldl insertWith (fun _ => none) =
      fromRows key rows := by
  simp only [List.foldl_map, fromRows]

/-- Reversing a singleton prepend gives the existing append insertion. -/
theorem reverse_insert_singleton [DecidableEq Key] (table : Table Key Item)
    (rowKey : Key) (row : Item) :
    reverseTable (insertWith table (rowKey, [row])) =
      SourceCurrentMergeGrouping.insertWith (reverseTable table) (rowKey, [row]) := by
  funext query
  by_cases same : query = rowKey
  · simp only [reverseTable, insertWith, SourceCurrentMergeGrouping.insertWith, same, ↓reduceIte]
    cases table rowKey <;> simp
  · simp only [reverseTable, insertWith, SourceCurrentMergeGrouping.insertWith, same, ↓reduceIte]

/-- Bucket reversal commutes with the whole singleton fold from any initial table. -/
theorem reverse_fold [DecidableEq Key] (key : Item → Key) (rows : List Item)
    (table : Table Key Item) :
    reverseTable (rows.foldl (fun table row => insertWith table (key row, [row])) table) =
      rows.foldl (fun table row => SourceCurrentMergeGrouping.insertWith table (key row, [row]))
        (reverseTable table) := by
  induction rows generalizing table with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.foldl_cons]
      rw [ih, reverse_insert_singleton]

/-- Final bucket reversal gives the existing empty-table grouping exactly. -/
theorem reverse_fromRows [DecidableEq Key] (key : Item → Key) (rows : List Item) :
    reverseTable (fromRows key rows) = SourceCurrentMergeGrouping.fromRows key rows := by
  unfold fromRows SourceCurrentMergeGrouping.fromRows
  rw [reverse_fold]
  apply congrArg (fun table : Table Key Item =>
    rows.foldl (fun table row => SourceCurrentMergeGrouping.insertWith table (key row, [row])) table)
  funext query
  rfl

/-- Reverse each emitted bucket and retain its exact lookup key and iteration order. -/
theorem iteration_reverse (table : Table Key Item) (entries : List (Key × List Item))
    (iteration : Iteration table entries) :
    Iteration (reverseTable table) (entries.map (fun entry => (entry.1, entry.2.reverse))) := by
  refine ⟨?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def] using iteration.unique
  · intro query bucket
    constructor
    · intro included
      obtain ⟨entry, original, same⟩ := List.mem_map.mp included
      cases entry with
      | mk storedKey storedBucket =>
          cases same
          exact congrArg (Option.map List.reverse)
            ((iteration.lookup storedKey storedBucket).mp original)
    · intro found
      obtain ⟨storedBucket, stored, same⟩ := Option.map_eq_some_iff.mp found
      exact List.mem_map.mpr ⟨(query, storedBucket),
        (iteration.lookup query storedBucket).mpr stored, Prod.ext rfl same⟩

/-- Reversed prepend buckets permute the existing complete canonical groups. -/
theorem iteration_permutation [DecidableEq Key] (key : Item → Key) (rows : List Item)
    (entries : List (Key × List Item)) (iteration : Iteration (fromRows key rows) entries) :
    ((entries.map Prod.snd).map List.reverse).Perm (Sized.groups key rows) := by
  simpa only [List.map_map, Function.comp_def] using
    SourceCurrentMergeGrouping.Iteration.permutation key rows
      (entries.map (fun entry => (entry.1, entry.2.reverse)))
      (by simpa only [reverse_fromRows] using
        iteration_reverse (fromRows key rows) entries iteration)

end MicroCFTA.SourceCurrentPrependGrouping

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentPrependGrouping.insertWith
#print MicroCFTA.SourceCurrentPrependGrouping.insertWith
#print axioms MicroCFTA.SourceCurrentPrependGrouping.insertWith
#check @MicroCFTA.SourceCurrentPrependGrouping.fromRows
#print MicroCFTA.SourceCurrentPrependGrouping.fromRows
#print axioms MicroCFTA.SourceCurrentPrependGrouping.fromRows
#check @MicroCFTA.SourceCurrentPrependGrouping.reverseTable
#print MicroCFTA.SourceCurrentPrependGrouping.reverseTable
#print axioms MicroCFTA.SourceCurrentPrependGrouping.reverseTable
#check @MicroCFTA.SourceCurrentPrependGrouping.pair_fold
#print MicroCFTA.SourceCurrentPrependGrouping.pair_fold
#print axioms MicroCFTA.SourceCurrentPrependGrouping.pair_fold
#check @MicroCFTA.SourceCurrentPrependGrouping.reverse_insert_singleton
#print MicroCFTA.SourceCurrentPrependGrouping.reverse_insert_singleton
#print axioms MicroCFTA.SourceCurrentPrependGrouping.reverse_insert_singleton
#check @MicroCFTA.SourceCurrentPrependGrouping.reverse_fold
#print MicroCFTA.SourceCurrentPrependGrouping.reverse_fold
#print axioms MicroCFTA.SourceCurrentPrependGrouping.reverse_fold
#check @MicroCFTA.SourceCurrentPrependGrouping.reverse_fromRows
#print MicroCFTA.SourceCurrentPrependGrouping.reverse_fromRows
#print axioms MicroCFTA.SourceCurrentPrependGrouping.reverse_fromRows
#check @MicroCFTA.SourceCurrentPrependGrouping.iteration_reverse
#print MicroCFTA.SourceCurrentPrependGrouping.iteration_reverse
#print axioms MicroCFTA.SourceCurrentPrependGrouping.iteration_reverse
#check @MicroCFTA.SourceCurrentPrependGrouping.iteration_permutation
#print MicroCFTA.SourceCurrentPrependGrouping.iteration_permutation
#print axioms MicroCFTA.SourceCurrentPrependGrouping.iteration_permutation
