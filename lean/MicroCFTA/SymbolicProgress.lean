import MicroCFTA.SymbolicCounting

/-!
# Progress of symbolic domain rewrites

A positive graph budget bounds the number of constructor nodes in a domain.
Each child tuple has smaller total budget than its parent. Intersection never
increases a domain budget. These are structural graph obligations, not count
or decoder correctness assumptions.
-/
namespace MicroCFTA.SymbolicDriver
open Symbolic (Fragment)

/-- Sum the structural budgets of all independent live domains. -/
def domainBudget (budget : Nat → Nat) (domains : List (Nat × Nat)) : Nat :=
  (domains.map fun entry => budget entry.2).sum

/-- Sorting a domain map does not change its structural budget. -/
theorem domainBudget_sort (budget : Nat → Nat) (domains : List (Nat × Nat)) :
    domainBudget budget (domains.mergeSort fun left right => left.1 ≤ right.1) = domainBudget budget domains := by
  exact ((List.mergeSort_perm domains _).map (fun entry => budget entry.2)).sum_nat

/-- A domain map without the selected name is unchanged by deletion. -/
theorem delete_absent (entries : List (Nat × Value)) (name : Nat) (absent : name ∉ entries.map Prod.fst) :
    delete entries name = entries := by
  unfold delete
  apply List.filter_eq_self.mpr
  intro entry member
  have different : entry.1 ≠ name := by
    intro same
    exact absent (List.mem_map.mpr ⟨entry, member, same⟩)
  simpa using different

/-- Removing one distinct live name removes exactly its domain budget. -/
theorem domainBudget_delete (budget : Nat → Nat) (domains : List (Nat × Nat))
    (distinct : (domains.map Prod.fst).Nodup) (name node : Nat) (member : (name, node) ∈ domains) :
    domainBudget budget domains = budget node + domainBudget budget (delete domains name) := by
  induction domains with
  | nil => cases member
  | cons entry rest ih =>
      have unique := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with same | inside
      · subst entry
        have noTail := delete_absent rest name unique.1
        simp [domainBudget, delete]
        change (List.map (fun entry => budget entry.2) rest).sum =
          (List.map (fun entry => budget entry.2) (delete rest name)).sum
        rw [noTail]
      · have unequal : entry.1 ≠ name := fun same =>
          unique.1 (List.mem_map.mpr ⟨(name, node), inside, same.symm⟩)
        have smaller := ih unique.2 inside
        simp [domainBudget, delete, unequal] at smaller ⊢
        omega

/-- Replacing a cached domain uses the new budget and retains all other names. -/
theorem domainBudget_insert (budget : Nat → Nat) (domains : List (Nat × Nat)) (name node : Nat) :
    domainBudget budget (insert domains name node) = budget node + domainBudget budget (delete domains name) := by
  unfold insert
  rw [domainBudget_sort]
  simp [domainBudget]

/-- Deleting distinct names commutes. -/
theorem delete_commute (entries : List (Nat × Value)) (left right : Nat) :
    delete (delete entries left) right = delete (delete entries right) left := by
  simp [delete, List.filter_filter, Bool.and_comm]

/-- Deletion preserves the distinct live-name invariant. -/
theorem delete_distinct (entries : List (Nat × Value)) (distinct : (entries.map Prod.fst).Nodup) (name : Nat) :
    ((delete entries name).map Prod.fst).Nodup := by
  exact List.Nodup.sublist ((List.filter_sublist).map _) distinct

/-- A different domain survives deletion of the merged variable. -/
theorem member_delete_other (entries : List (Nat × Value)) (removed name : Nat) (value : Value)
    (different : name ≠ removed) (member : (name, value) ∈ entries) :
    (name, value) ∈ delete entries removed := by
  simp [delete, member, different]

/-- Whole-variable unification strictly decreases the live budget before the next solve call. -/
theorem unify_variables_progress (budget : Nat → Nat) (domains : List (Nat × Nat))
    (distinct : (domains.map Prod.fst).Nodup) (left right leftNode rightNode common : Nat)
    (different : left ≠ right) (leftMember : (left, leftNode) ∈ domains)
    (rightMember : (right, rightNode) ∈ domains)
    (positive : 0 < budget leftNode) (intersection : budget common ≤ budget rightNode) :
    domainBudget budget (insert (delete domains left) right common) < domainBudget budget domains := by
  have removeLeft := domainBudget_delete budget domains distinct left leftNode leftMember
  have removeRight := domainBudget_delete budget (delete domains left) (delete_distinct domains distinct left)
    right rightNode (member_delete_other domains left right rightNode (Ne.symm different) rightMember)
  rw [domainBudget_insert]
  omega

/-- Fresh names paired with children retain exactly the children's structural budget. -/
theorem fresh_children_budget (budget : Nat → Nat) (next : Nat) (children : List Nat) :
    domainBudget budget ((List.range' next children.length).zip children) = (children.map budget).sum := by
  unfold domainBudget
  have pairs : (((List.range' next children.length).zip children).map Prod.snd) = children := by
    apply List.map_snd_zip
    simp
  have same := congrArg (List.map budget) pairs
  simpa only [List.map_map, Function.comp_def] using congrArg List.sum same

/-- Expanding a variable strictly decreases the budget even when its new domains increase in number. -/
theorem expand_variable_progress (budget : Nat → Nat) (domains : List (Nat × Nat))
    (distinct : (domains.map Prod.fst).Nodup) (name node next : Nat) (children : List Nat)
    (member : (name, node) ∈ domains) (edgeSmaller : (children.map budget).sum < budget node) :
    domainBudget budget ((((List.range' next children.length).zip children) ++ delete domains name).mergeSort
      (fun left right => left.1 ≤ right.1)) < domainBudget budget domains := by
  rw [domainBudget_sort]
  have removed := domainBudget_delete budget domains distinct name node member
  have childrenBudget := fresh_children_budget budget next children
  simp only [domainBudget, List.map_append, List.sum_append] at childrenBudget ⊢
  unfold domainBudget at removed
  omega

/-- Alpha-normalization does not reset or increase the structural progress measure. -/
theorem normalize_preserves_budget [DecidableEq Symbol] [Ord Symbol] (budget : Nat → Nat)
    (fuel : Nat) (problem normalized : Problem Symbol)
    (success : normalize fuel problem = .ok (some normalized)) :
    domainBudget budget normalized.domains = domainBudget budget problem.domains := by
  have same := congrArg (List.map budget) (normalize_preserves_graph_domains fuel problem normalized success)
  simpa only [domainBudget, List.map_map, Function.comp_def] using congrArg List.sum same

/-- Insertion preserves the source map's distinct-key invariant. -/
theorem insert_distinct (entries : List (Nat × Value)) (distinct : (entries.map Prod.fst).Nodup)
    (name : Nat) (value : Value) : ((insert entries name value).map Prod.fst).Nodup := by
  unfold insert
  apply ((List.mergeSort_perm ((name, value) :: delete entries name) _).map Prod.fst).nodup_iff.mpr
  apply List.nodup_cons.mpr
  refine ⟨?_, delete_distinct entries distinct name⟩
  simp [delete, List.mem_map, List.mem_filter]

/-- Every fresh child name differs from every existing live name. -/
theorem expand_variables_fresh (domains : List (Nat × Nat))
    (distinct : (domains.map Prod.fst).Nodup) (name next : Nat) (children : List Nat)
    (fresh : ∀ entry ∈ domains, entry.1 < next) :
    (((((List.range' next children.length).zip children) ++ delete domains name).mergeSort
      (fun left right => left.1 ≤ right.1)).map Prod.fst).Nodup := by
  apply ((List.mergeSort_perm (((List.range' next children.length).zip children) ++ delete domains name) _).map Prod.fst).nodup_iff.mpr
  rw [List.map_append, List.map_fst_zip (by simp)]
  apply List.nodup_append.mpr
  refine ⟨List.nodup_range', delete_distinct domains distinct name, ?_⟩
  intro new newMember old oldMember same
  obtain ⟨offset, _, newEqual⟩ := List.mem_range'.mp newMember
  obtain ⟨entry, entryMember, oldEqual⟩ := List.mem_map.mp oldMember
  have original : entry ∈ domains := (List.mem_filter.mp entryMember).1
  have older := fresh entry original
  omega

/-- The source occurrence test on fresh child variables is ordinary name membership. -/
theorem occursMany_variables (name : Nat) (names : List Nat) :
    occursMany name (names.map (Fragment.var (Symbol := Symbol))) = true ↔ name ∈ names := by
  induction names with
  | nil => simp [occursMany]
  | cons first rest ih => simp [occursMany, occurs, ih]

/-- A fresh expansion cannot create a substitution cycle through its removed variable. -/
theorem expansion_binding_acyclic (name next : Nat) (symbol : Symbol) (arity : Nat)
    (older : name < next) :
    occurs name (.constructor symbol ((List.range' next arity).map Fragment.var)) = false := by
  have absent : name ∉ List.range' next arity := by
    intro member
    obtain ⟨offset, _, same⟩ := List.mem_range'.mp member
    omega
  have notOccurs : occursMany name ((List.range' next arity).map (Fragment.var (Symbol := Symbol))) ≠ true :=
    fun yes => absent ((occursMany_variables name _).mp yes)
  cases result : occurs name (.constructor symbol ((List.range' next arity).map Fragment.var))
  · rfl
  · exact False.elim (notOccurs result)

end MicroCFTA.SymbolicDriver
