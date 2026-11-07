import MicroCFTA.CanonicalClasses
import MicroCFTA.SourceCurrentMergeGrouping

/-!
# Ascending readback of append buckets

The source map groups singleton values with `fromListWith (flip (<>))`.
Each bucket retains its input order. Ascending key readback changes only
the order of complete buckets. Repeated input values remain repeated.
-/
namespace MicroCFTA.SourceSortedBuckets
open Std

variable {Key Value : Type} [DecidableEq Key] [Ord Key]

/-- Read each source key once in ascending order. -/
def keys (keyOf : Value → Key) (values : List Value) : List Key :=
  CanonicalClasses.sortedSet (values.map keyOf)

/-- Read each complete bucket in its original value order. -/
def buckets (keyOf : Value → Key) (values : List Value) : List (Key × List Value) :=
  (keys keyOf values).map fun key => (key, values.filter fun value => decide (keyOf value = key))

/-- Concatenate complete buckets in ascending key order. -/
def gather (keyOf : Value → Key) (values : List Value) : List Value :=
  (keys keyOf values).flatMap fun key => values.filter fun value => decide (keyOf value = key)

/-- Readback contains precisely the keys that occur in the input. -/
theorem mem_keys (keyOf : Value → Key) (values : List Value) (key : Key) :
    key ∈ keys keyOf values ↔ key ∈ values.map keyOf :=
  CanonicalClasses.mem_sortedSet (values.map keyOf) key

/-- Each key occurs once even when the input has repeated values. -/
theorem keys_nodup (keyOf : Value → Key) (values : List Value) : (keys keyOf values).Nodup :=
  CanonicalClasses.sortedSet_nodup (values.map keyOf)

/-- Transitive source comparison gives ascending key readback. -/
theorem keys_ordered [TransOrd Key] (keyOf : Value → Key) (values : List Value) :
    (keys keyOf values).Pairwise (fun left right => (compare left right).isLE = true) :=
  CanonicalClasses.sortedSet_ordered (values.map keyOf)

/-- Bucket entries have exactly the canonical key sequence. -/
theorem buckets_keys (keyOf : Value → Key) (values : List Value) :
    (buckets keyOf values).map Prod.fst = keys keyOf values := by
  simp [buckets, List.map_map, Function.comp_def]

/-- A bucket is the exact input filter at its declared key. -/
theorem bucket_exact (keyOf : Value → Key) (values : List Value) (key : Key) (bucket : List Value) :
    (key, bucket) ∈ buckets keyOf values ↔
      key ∈ values.map keyOf ∧ bucket = values.filter (fun value => decide (keyOf value = key)) := by
  constructor
  · intro member
    obtain ⟨query, present, same⟩ := List.mem_map.mp member
    have sameKey : query = key := congrArg Prod.fst same
    subst query
    exact ⟨(mem_keys keyOf values key).mp present, (congrArg Prod.snd same).symm⟩
  · rintro ⟨present, rfl⟩
    exact List.mem_map.mpr ⟨key, (mem_keys keyOf values key).mpr present, rfl⟩

/-- Sorted readback agrees with the existing source append-fold lookup. -/
theorem buckets_lookup (keyOf : Value → Key) (values : List Value) (key : Key) (bucket : List Value) :
    (key, bucket) ∈ buckets keyOf values ↔
      SourceCurrentMergeGrouping.fromRows keyOf values key = some bucket :=
  (bucket_exact keyOf values key bucket).trans
    (SourceCurrentMergeGrouping.lookup_some keyOf values key bucket).symm

/-- Ascending buckets instantiate the existing exact finite map iterator. -/
theorem iteration (keyOf : Value → Key) (values : List Value) :
    SourceCurrentMergeGrouping.Iteration
      (SourceCurrentMergeGrouping.fromRows keyOf values) (buckets keyOf values) := by
  refine ⟨?_, ?_⟩
  · rw [buckets_keys]
    exact keys_nodup keyOf values
  · exact buckets_lookup keyOf values

private theorem gather_flatten (keyOf : Value → Key) (values : List Value) :
    ((buckets keyOf values).map Prod.snd).flatten = gather keyOf values := by
  unfold buckets gather
  generalize keys keyOf values = ordered
  induction ordered with
  | nil => rfl
  | cons key rest ih =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]

/-- Sorted grouping preserves every occurrence, with no input distinctness premise. -/
theorem gather_perm (keyOf : Value → Key) (values : List Value) :
    (gather keyOf values).Perm values := by
  rw [← gather_flatten keyOf values]
  have grouped := SourceCurrentMergeGrouping.Iteration.permutation keyOf values
    (buckets keyOf values) (iteration keyOf values)
  exact grouped.flatten.trans (Sized.groups_perm keyOf values)

/-- Selecting keys retains their complete buckets and their ascending order. -/
theorem gather_filter (keyOf : Value → Key) (values : List Value) (predicate : Key → Bool) :
    (gather keyOf values).filter (fun value => predicate (keyOf value)) =
      ((keys keyOf values).filter predicate).flatMap
        (fun key => values.filter fun value => decide (keyOf value = key)) := by
  let bucket (key : Key) := values.filter fun value => decide (keyOf value = key)
  have selected (key : Key) :
      (bucket key).filter (fun value => predicate (keyOf value)) =
        if predicate key then bucket key else [] := by
    have same : (bucket key).filter (fun value => predicate (keyOf value)) =
        (bucket key).filter (fun _ => predicate key) := by
      apply List.filter_congr
      intro value member
      have atKey : keyOf value = key := of_decide_eq_true (List.mem_filter.mp member).2
      rw [atKey]
    rw [same]
    cases predicate key <;> simp
  change ((keys keyOf values).flatMap bucket).filter (fun value => predicate (keyOf value)) =
    ((keys keyOf values).filter predicate).flatMap bucket
  generalize keys keyOf values = ordered
  induction ordered with
  | nil => rfl
  | cons key rest ih =>
      simp only [List.flatMap_cons, List.filter_append, selected key]
      cases kept : predicate key <;> simp [kept, ih]

end MicroCFTA.SourceSortedBuckets
