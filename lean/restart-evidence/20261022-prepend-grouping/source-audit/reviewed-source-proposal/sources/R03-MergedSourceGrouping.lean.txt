import MicroCFTA.MergedPhysicalGroupRoot
import MicroCFTA.Sized

/-!
# Derived complete symbol and arity groups

The existing executable partition preserves each full key class in input
order. A source-style append fold has exactly those buckets. Any outer
permutation retains the structural grouping contract.
-/
namespace MicroCFTA.MergedSourceGrouping
open InternedConstructorTemplates MergedPhysicalGroupRoot
variable {Key Item : Type}

/-- Each executable partition class is the complete input filter at its first key. -/
theorem groups_exact [DecidableEq Key] (key : Item → Key) (items : List Item) :
    ∀ group ∈ Sized.groups key items, ∃ first rest, group = first :: rest ∧
      group = items.filter (fun item => decide (key item = key first)) := by
  induction items using Sized.groups.induct key with
  | case1 => simp [Sized.groups]
  | case2 first rest ih =>
      rw [List.unattach_filter (g := fun other => decide (key other ≠ key first))
        (hf := fun _ _ => rfl), List.unattach_attach] at ih
      intro group member
      rw [Sized.groups] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨first, _, rfl, by simp⟩
      · obtain ⟨next, tail, same, exactGroup⟩ := ih group member
        have nextIn : next ∈ rest.filter (fun other => decide (key other ≠ key first)) := by
          apply (Sized.groups_perm key _).mem_iff.mp
          exact List.mem_flatten.mpr ⟨group, member, by simp [same]⟩
        have different : key next ≠ key first := of_decide_eq_true (List.mem_filter.mp nextIn).2
        refine ⟨next, tail, same, ?_⟩
        rw [exactGroup, List.filter_filter]
        simp only [List.filter_cons, decide_eq_true_eq, Ne.symm different, ↓reduceIte]
        apply List.filter_congr
        intro item included
        by_cases equal : key item = key next
        · simp [equal, different]
        · simp [equal]

/-- Group on the exact source symbol and child-count pair. -/
def groupKey (edge : EdgeValue Symbol Guard) : Symbol × Nat :=
  (edge.entry.key.symbol, edge.children.length)

/-- The existing finite partition supplies an executable source grouping. -/
def groups [DecidableEq Symbol] (edges : List (EdgeValue Symbol Guard)) : List (List (EdgeValue Symbol Guard)) :=
  Sized.groups groupKey edges

/-- The full source grouping contract follows from executable partitioning. -/
theorem groups_correct [DecidableEq Symbol] (edges : List (EdgeValue Symbol Guard)) :
    Grouping edges (groups edges) := by
  refine ⟨Sized.groups_perm groupKey edges, ?_⟩
  intro group member
  obtain ⟨first, rest, same, complete⟩ := groups_exact groupKey edges group member
  exact ⟨first, rest, same, by simpa only [groupKey, Prod.mk.injEq] using complete⟩

/-- Hash-table iteration can permute whole buckets while retaining exact within-bucket order. -/
theorem grouping_permutation [DecidableEq Symbol] (edges : List (EdgeValue Symbol Guard))
    (order : List (List (EdgeValue Symbol Guard))) (permutation : order.Perm (groups edges)) :
    Grouping edges order :=
  ⟨permutation.flatten.trans (groups_correct edges).partition,
    fun group member => (groups_correct edges).exact group (permutation.mem_iff.mp member)⟩

/-- Append the next source row to its bucket, as `fromListWith (flip (++))` does. -/
def appendBucket [DecidableEq Key] (key : Item → Key) (table : Key → List Item) (item : Item) : Key → List Item :=
  fun query => if key item = query then table query ++ [item] else table query

/-- The ordered source insertion fold retains exactly the filtered suffix in each bucket. -/
theorem fold_bucket [DecidableEq Key] (key : Item → Key) (items : List Item)
    (table : Key → List Item) (query : Key) :
    (items.foldl (appendBucket key) table) query = table query ++ items.filter (fun item => decide (key item = query)) := by
  induction items generalizing table with
  | nil => simp
  | cons first rest ih =>
      rw [List.foldl_cons, ih]
      by_cases same : key first = query <;> simp [appendBucket, same, List.append_assoc]

/-- Starting from an empty source map gives the exact bucket used by the grouping proof. -/
theorem empty_bucket [DecidableEq Key] (key : Item → Key) (items : List Item) (query : Key) :
    (items.foldl (appendBucket key) (fun _ => [])) query = items.filter (fun item => decide (key item = query)) := by
  simpa using fold_bucket key items (fun _ => []) query

end MicroCFTA.MergedSourceGrouping
