import MicroCFTA.MergedSourceGrouping

/-!
# Ordered merge buckets and finite map iteration

The source inserts singleton rows with `flip (++)`. An old bucket precedes
its new row. The optional lookup retains the distinction between an absent
key and a stored list. Finite iteration lists every stored key once.

The iteration contract below is a container boundary. The proofs derive
bucket permutation from that contract. They do not implement Haskell
HashMap storage or identify constructor heaps from different bucket orders.
-/
namespace MicroCFTA.SourceCurrentMergeGrouping
open InternedConstructorTemplates
variable {Key Item : Type}

/-- Optional lookup distinguishes an absent source key from a stored bucket. -/
abbrev Table (Key Item : Type) := Key → Option (List Item)

/-- Source insertion combines a new list with the old list as old followed by new. -/
def insertWith [DecidableEq Key] (table : Table Key Item) (entry : Key × List Item) : Table Key Item :=
  fun query => if query = entry.1 then some ((table query).getD [] ++ entry.2) else table query

/-- Source singleton insertion retains the input traversal order. -/
def fromRows [DecidableEq Key] (key : Item → Key) (rows : List Item) : Table Key Item :=
  rows.foldl (fun table row => insertWith table (key row, [row])) (fun _ => none)

/-- The singleton fold is exactly the source pair-list `fromListWith` schedule. -/
theorem pair_fold [DecidableEq Key] (key : Item → Key) (rows : List Item) :
    (rows.map (fun row => (key row, [row]))).foldl insertWith (fun _ => none) = fromRows key rows := by
  simp only [List.foldl_map, fromRows]

/-- Insertion gives the same ordered bucket equation as the existing append fold. -/
theorem fold_default [DecidableEq Key] (key : Item → Key) (rows : List Item)
    (table : Table Key Item) (query : Key) :
    ((rows.foldl (fun table row => insertWith table (key row, [row])) table) query).getD [] =
      (table query).getD [] ++ rows.filter (fun row => decide (key row = query)) := by
  induction rows generalizing table with
  | nil => simp
  | cons first rest ih =>
      rw [List.foldl_cons, ih]
      by_cases same : key first = query
      · simp [insertWith, same, List.append_assoc]
      · simp [insertWith, same, Ne.symm same]

/-- A key stays absent exactly when neither the initial table nor a source row supplies it. -/
theorem fold_none [DecidableEq Key] (key : Item → Key) (rows : List Item)
    (table : Table Key Item) (query : Key) :
    (rows.foldl (fun table row => insertWith table (key row, [row])) table) query = none ↔
      table query = none ∧ query ∉ rows.map key := by
  induction rows generalizing table with
  | nil => simp
  | cons first rest ih =>
      rw [List.foldl_cons, ih]
      by_cases same : key first = query
      · simp [insertWith, same]
      · simp [insertWith, Ne.symm same]

/-- Reading a completed bucket retains every matching input occurrence in its original order. -/
theorem lookup_default [DecidableEq Key] (key : Item → Key) (rows : List Item) (query : Key) :
    (fromRows key rows query).getD [] = rows.filter (fun row => decide (key row = query)) := by
  simpa only [fromRows, Option.getD_none, List.nil_append] using fold_default key rows (fun _ => none) query

/-- The source map domain is exactly the keys that occur in its input rows. -/
theorem lookup_none [DecidableEq Key] (key : Item → Key) (rows : List Item) (query : Key) :
    fromRows key rows query = none ↔ query ∉ rows.map key := by
  simpa only [fromRows, true_and] using fold_none key rows (fun _ => none) query

/-- A stored lookup has the exact nonempty source bucket, including repeated rows. -/
theorem lookup_some [DecidableEq Key] (key : Item → Key) (rows : List Item) (query : Key) (bucket : List Item) :
    fromRows key rows query = some bucket ↔
      query ∈ rows.map key ∧ bucket = rows.filter (fun row => decide (key row = query)) := by
  constructor
  · intro found
    have member : query ∈ rows.map key := by
      by_cases present : query ∈ rows.map key
      · exact present
      · rw [(lookup_none key rows query).mpr present] at found
        cases found
    have contents := lookup_default key rows query
    rw [found] at contents
    exact ⟨member, contents⟩
  · rintro ⟨member, rfl⟩
    cases found : fromRows key rows query with
    | none => exact False.elim ((lookup_none key rows query).mp found member)
    | some bucket =>
        have contents := lookup_default key rows query
        rw [found] at contents
        exact congrArg some contents

/-- Every stored bucket contains a row and thus has a well-defined physical group key. -/
theorem lookup_nonempty [DecidableEq Key] (key : Item → Key) (rows : List Item) (query : Key)
    (bucket : List Item) (found : fromRows key rows query = some bucket) : bucket ≠ [] := by
  obtain ⟨present, contents⟩ := (lookup_some key rows query bucket).mp found
  obtain ⟨first, member, same⟩ := List.mem_map.mp present
  have included : first ∈ bucket := by simp [contents, member, same]
  intro empty
  rw [empty] at included
  cases included

/-- Each stored row has its bucket's exact key. -/
theorem lookup_key [DecidableEq Key] (key : Item → Key) (rows : List Item) (query : Key)
    (bucket : List Item) (found : fromRows key rows query = some bucket) :
    ∀ row ∈ bucket, key row = query := by
  obtain ⟨_, contents⟩ := (lookup_some key rows query bucket).mp found
  intro row member
  rw [contents] at member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- The canonical partition emits no repeated complete bucket. -/
theorem groups_nodup [DecidableEq Key] (key : Item → Key) (rows : List Item) :
    (Sized.groups key rows).Nodup := by
  induction rows using Sized.groups.induct key with
  | case1 => simp [Sized.groups]
  | case2 first rest ih =>
      rw [List.unattach_filter (g := fun other => decide (key other ≠ key first))
        (hf := fun _ _ => rfl), List.unattach_attach] at ih
      rw [Sized.groups, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro repeated
      have bad : first ∈ rest.filter (fun other => decide (key other ≠ key first)) :=
        (Sized.groups_perm key _).mem_iff.mp
          (List.mem_flatten.mpr ⟨_, repeated, List.mem_cons_self⟩)
      exact (of_decide_eq_true (List.mem_filter.mp bad).2) rfl

/-- Canonical groups and optional source lookups contain the same complete buckets. -/
theorem group_member [DecidableEq Key] (key : Item → Key) (rows : List Item) (bucket : List Item) :
    bucket ∈ Sized.groups key rows ↔ ∃ query, fromRows key rows query = some bucket := by
  constructor
  · intro included
    obtain ⟨first, rest, shape, exactBucket⟩ := MergedSourceGrouping.groups_exact key rows bucket included
    have original : first ∈ rows :=
      (Sized.groups_perm key rows).mem_iff.mp (List.mem_flatten.mpr ⟨bucket, included, by simp [shape]⟩)
    exact ⟨key first, (lookup_some key rows (key first) bucket).mpr
      ⟨List.mem_map.mpr ⟨first, original, rfl⟩, exactBucket⟩⟩
  · rintro ⟨query, found⟩
    obtain ⟨present, contents⟩ := (lookup_some key rows query bucket).mp found
    obtain ⟨first, original, same⟩ := List.mem_map.mp present
    obtain ⟨group, included, firstIn⟩ := List.mem_flatten.mp ((Sized.groups_perm key rows).mem_iff.mpr original)
    obtain ⟨head, rest, _, exactGroup⟩ := MergedSourceGrouping.groups_exact key rows group included
    have firstKey : key first = key head := by
      rw [exactGroup] at firstIn
      exact of_decide_eq_true (List.mem_filter.mp firstIn).2
    have queryKey : query = key head := same.symm.trans firstKey
    have equal : bucket = group := by rw [contents, exactGroup, queryKey]
    exact equal ▸ included

/-- A finite map iterator returns every stored entry once at its literal lookup key. -/
structure Iteration (table : Table Key Item) (entries : List (Key × List Item)) : Prop where
  unique : (entries.map Prod.fst).Nodup
  lookup : ∀ query bucket, (query, bucket) ∈ entries ↔ table query = some bucket

/-- Unique emitted keys and exact lookup imply unique emitted buckets for this source map. -/
theorem Iteration.buckets_nodup [DecidableEq Key] (key : Item → Key) (rows : List Item)
    (entries : List (Key × List Item)) (iteration : Iteration (fromRows key rows) entries) :
    (entries.map Prod.snd).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.pairwise_map.mp iteration.unique).imp_of_mem
  intro left right leftIn rightIn different equal
  have leftLookup := (iteration.lookup left.1 left.2).mp leftIn
  have rightLookup := (iteration.lookup right.1 right.2).mp rightIn
  obtain ⟨first, rest, shape⟩ := List.exists_cons_of_ne_nil (lookup_nonempty key rows left.1 left.2 leftLookup)
  have firstIn : first ∈ left.2 := by simp [shape]
  have leftKey := lookup_key key rows left.1 left.2 leftLookup first firstIn
  have rightKey := lookup_key key rows right.1 right.2 rightLookup first (equal ▸ firstIn)
  exact different (leftKey.symm.trans rightKey)

/-- The exact finite iterator emits a permutation of the canonical buckets, without fixing its order. -/
theorem Iteration.permutation [DecidableEq Key] (key : Item → Key) (rows : List Item)
    (entries : List (Key × List Item)) (iteration : Iteration (fromRows key rows) entries) :
    (entries.map Prod.snd).Perm (Sized.groups key rows) := by
  apply (List.perm_ext_iff_of_nodup (iteration.buckets_nodup key rows entries) (groups_nodup key rows)).mpr
  intro bucket
  constructor
  · intro present
    obtain ⟨entry, member, same⟩ := List.mem_map.mp present
    exact (group_member key rows bucket).mpr ⟨entry.1, same ▸ (iteration.lookup entry.1 entry.2).mp member⟩
  · intro present
    obtain ⟨query, found⟩ := (group_member key rows bucket).mp present
    exact List.mem_map.mpr ⟨(query, bucket), (iteration.lookup query bucket).mpr found, rfl⟩

/-- Literal merge-key insertion and exact iteration derive the existing physical grouping contract. -/
theorem merge_grouping [DecidableEq Symbol] (edges : List (EdgeValue Symbol Guard))
    (entries : List ((Symbol × Nat) × List (EdgeValue Symbol Guard)))
    (iteration : Iteration (fromRows MergedSourceGrouping.groupKey edges) entries) :
    MergedPhysicalGroupRoot.Grouping edges (entries.map Prod.snd) :=
  MergedSourceGrouping.grouping_permutation edges _ (iteration.permutation MergedSourceGrouping.groupKey edges entries)

end MicroCFTA.SourceCurrentMergeGrouping
