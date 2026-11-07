import MicroCFTA.SourceSortedBuckets

/-!
# Exact per-key projection after sorted grouping

Ascending readback moves complete buckets. Filtering the result at one
key therefore retains the input order and every repeated value.
-/
namespace MicroCFTA.SourceSortedBucketsProjection
open SourceSortedBuckets

variable {Key Value : Type} [DecidableEq Key] [Ord Key]

omit [Ord Key] in
private theorem filter_singleton (items : List Key) (distinct : items.Nodup) (key : Key) :
    items.filter (fun item => decide (item = key)) = if key ∈ items then [key] else [] := by
  revert distinct
  induction items with
  | nil => intro _; simp
  | cons first rest ih =>
      intro distinct
      obtain ⟨separate, distinctRest⟩ := List.nodup_cons.mp distinct
      by_cases same : first = key
      · subst first
        simp [ih distinctRest, separate]
      · simp [same, Ne.symm same, ih distinctRest]

/-- A projected bucket retains exactly the input values in their input order. -/
theorem gather_at_key (keyOf : Value → Key) (values : List Value) (key : Key) :
    (gather keyOf values).filter (fun value => decide (keyOf value = key)) =
      values.filter (fun value => decide (keyOf value = key)) := by
  rw [gather_filter keyOf values (fun query => decide (query = key)),
    filter_singleton (keys keyOf values) (keys_nodup keyOf values) key]
  by_cases present : key ∈ keys keyOf values
  · simp [present]
  · have empty : values.filter (fun value => decide (keyOf value = key)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro value member
      obtain ⟨included, same⟩ := List.mem_filter.mp member
      exact present ((mem_keys keyOf values key).mpr
        (List.mem_map.mpr ⟨value, included, of_decide_eq_true same⟩))
    simp [present, empty]

/-- Defaulted source lookup is the exact per-key projection of sorted readback. -/
theorem gather_lookup (keyOf : Value → Key) (values : List Value) (key : Key) :
    (SourceCurrentMergeGrouping.fromRows keyOf values key).getD [] =
      (gather keyOf values).filter (fun value => decide (keyOf value = key)) := by
  rw [gather_at_key]
  exact SourceCurrentMergeGrouping.lookup_default keyOf values key

/-- Optional lookup additionally records whether the key occurs in the input. -/
theorem gather_lookup_some (keyOf : Value → Key) (values : List Value)
    (key : Key) (bucket : List Value) :
    SourceCurrentMergeGrouping.fromRows keyOf values key = some bucket ↔
      key ∈ keys keyOf values ∧
        bucket = (gather keyOf values).filter (fun value => decide (keyOf value = key)) := by
  rw [SourceCurrentMergeGrouping.lookup_some, gather_at_key, mem_keys]

omit [Ord Key] in
/-- Appending emitted batches appends each old bucket before its new bucket. -/
theorem append_lookup (keyOf : Value → Key) (before after : List Value) (key : Key) :
    (SourceCurrentMergeGrouping.fromRows keyOf (before ++ after) key).getD [] =
      (SourceCurrentMergeGrouping.fromRows keyOf before key).getD [] ++
        (SourceCurrentMergeGrouping.fromRows keyOf after key).getD [] := by
  simp only [SourceCurrentMergeGrouping.lookup_default, List.filter_append]

end MicroCFTA.SourceSortedBucketsProjection
