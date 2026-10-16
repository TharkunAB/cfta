import MicroCFTA.SourceCurrentConjunctionEmptinessTable
import MicroCFTA.SourceEqualityNeededMap

/-!
# Literal conjunction insertion and ascending readback

The source builds an IntMap with one entry per resident identity.
Later entries replace earlier entries at the same key. Ascending iteration
then returns its values. The existing signed-map worker supplies this finite
map model. Native Patricia trees and machine identity conversion stay separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionMap
open SourceEqualityNeededMap
variable {Node : Type}

/-- Insert each original node in order, replacing the earlier value at its key. -/
def fromEntries (key : Node → Int) (nodes : List Node) (entries : List (Int × Node)) : List (Int × Node) :=
  nodes.foldl (fun entries node => alter (key node) (fun _ => node) entries) entries

/-- The source IntMap starts empty before its left-to-right insertion fold. -/
def fromList (key : Node → Int) (nodes : List Node) : List (Int × Node) := fromEntries key nodes []

/-- Source elems reads the completed map in ascending key order. -/
def elems (key : Node → Int) (nodes : List Node) : List Node := (fromList key nodes).map Prod.snd

/-- Every insertion retains the map's strict ascending key order. -/
theorem fromEntries_ascending (key : Node → Int) (nodes : List Node) (entries : List (Int × Node))
    (ordered : Ascending entries) : Ascending (fromEntries key nodes entries) := by
  induction nodes generalizing entries with
  | nil => exact ordered
  | cons node nodes ih => exact ih _ (alter_ascending _ _ _ ordered)

/-- The complete source insertion fold has one entry per key in ascending order. -/
theorem fromList_ascending (key : Node → Int) (nodes : List Node) : Ascending (fromList key nodes) :=
  fromEntries_ascending key nodes [] (by simp [Ascending])

/-- Exact lookup follows the source overwrite fold, including duplicate keys. -/
theorem fromEntries_lookup (key : Node → Int) (nodes : List Node) (entries : List (Int × Node))
    (ordered : Ascending entries) (query : Int) :
    lookup query (fromEntries key nodes entries) =
      nodes.foldl (fun found node => if query = key node then some node else found) (lookup query entries) := by
  induction nodes generalizing entries with
  | nil => rfl
  | cons node nodes ih =>
      rw [fromEntries, List.foldl_cons]
      rw [show nodes.foldl (fun entries node => alter (key node) (fun _ => node) entries)
          (alter (key node) (fun _ => node) entries) =
        fromEntries key nodes (alter (key node) (fun _ => node) entries) from rfl]
      rw [ih _ (alter_ascending _ _ _ ordered), lookup_alter _ _ _ _ ordered]
      rfl

/-- A lookup remains absent exactly when no initial or inserted key supplies it. -/
theorem fromEntries_none (key : Node → Int) (nodes : List Node) (entries : List (Int × Node))
    (ordered : Ascending entries) (query : Int) :
    lookup query (fromEntries key nodes entries) = none ↔
      lookup query entries = none ∧ ∀ node ∈ nodes, query ≠ key node := by
  induction nodes generalizing entries with
  | nil => simp [fromEntries]
  | cons node nodes ih =>
      change lookup query (fromEntries key nodes (alter (key node) (fun _ => node) entries)) = none ↔ _
      rw [ih _ (alter_ascending _ _ _ ordered), lookup_alter _ _ _ _ ordered]
      by_cases same : query = key node
      · simp [same]
      · simp [same]

/-- Any returned node comes from the initial map or from an actual inserted occurrence. -/
theorem fromEntries_origin (key : Node → Int) (nodes : List Node) (entries : List (Int × Node))
    (ordered : Ascending entries) (query : Int) (value : Node)
    (found : lookup query (fromEntries key nodes entries) = some value) :
    lookup query entries = some value ∨ value ∈ nodes ∧ key value = query := by
  induction nodes generalizing entries with
  | nil => exact Or.inl found
  | cons node nodes ih =>
      change lookup query (fromEntries key nodes (alter (key node) (fun _ => node) entries)) = some value at found
      rcases ih _ (alter_ascending _ _ _ ordered) found with first | inserted
      · rw [lookup_alter _ _ _ _ ordered] at first
        by_cases same : query = key node
        · simp only [same, ite_true, Option.some.injEq] at first
          subst value
          exact Or.inr ⟨List.mem_cons_self, same.symm⟩
        · exact Or.inl (by simpa only [same, ite_false] using first)
      · exact Or.inr ⟨List.mem_cons_of_mem _ inserted.1, inserted.2⟩

/-- A completed empty-start map returns only original nodes at their actual keys. -/
theorem fromList_origin (key : Node → Int) (nodes : List Node) (query : Int) (value : Node)
    (found : lookup query (fromList key nodes) = some value) : value ∈ nodes ∧ key value = query := by
  rcases fromEntries_origin key nodes [] (by simp [Ascending]) query value found with impossible | inserted
  · cases impossible
  · exact inserted

/-- A suffix without the queried key leaves the earlier winner unchanged. -/
theorem fromEntries_unchanged (key : Node → Int) (nodes : List Node) (entries : List (Int × Node))
    (ordered : Ascending entries) (query : Int) (absent : ∀ node ∈ nodes, query ≠ key node) :
    lookup query (fromEntries key nodes entries) = lookup query entries := by
  induction nodes generalizing entries with
  | nil => rfl
  | cons node nodes ih =>
      change lookup query (fromEntries key nodes (alter (key node) (fun _ => node) entries)) = _
      rw [ih _ (alter_ascending _ _ _ ordered) (fun value member => absent value (List.mem_cons_of_mem _ member))]
      simp only [lookup_alter _ _ _ _ ordered, absent node List.mem_cons_self, ite_false]

/-- The last matching source occurrence is the exact returned winner. -/
theorem last_winner (key : Node → Int) (earlier suffix : List Node) (node : Node)
    (last : ∀ later ∈ suffix, key node ≠ key later) :
    lookup (key node) (fromList key (earlier ++ node :: suffix)) = some node := by
  change lookup (key node) ((earlier ++ node :: suffix).foldl
    (fun entries node => alter (key node) (fun _ => node) entries) []) = some node
  rw [List.foldl_append, List.foldl_cons]
  change lookup (key node) (fromEntries key suffix
    (alter (key node) (fun _ => node) (fromList key earlier))) = some node
  rw [fromEntries_unchanged key suffix _
    (alter_ascending _ _ _ (fromList_ascending key earlier)) _ last]
  simp only [lookup_alter _ _ _ _ (fromList_ascending key earlier), ite_true]

/-- Key faithfulness on the actual input permits exact value readback. -/
def FaithfulOn (key : Node → Int) (nodes : List Node) : Prop :=
  ∀ left ∈ nodes, ∀ right ∈ nodes, key left = key right → left = right

/-- Under faithful keys, ascending elems retains exactly the original node set. -/
theorem mem_elems (key : Node → Int) (nodes : List Node) (faithful : FaithfulOn key nodes) (node : Node) :
    node ∈ elems key nodes ↔ node ∈ nodes := by
  constructor
  · intro member
    obtain ⟨entry, present, same⟩ := List.mem_map.mp member
    have found := lookup_of_mem entry.1 (fromList key nodes) entry.2 (fromList_ascending key nodes) present
    exact same ▸ (fromList_origin key nodes entry.1 entry.2 found).1
  · intro member
    have present : lookup (key node) (fromList key nodes) ≠ none := by
      intro missing
      have absent := ((fromEntries_none key nodes [] (by simp [Ascending]) (key node)).mp missing).2
      exact absent node member rfl
    cases found : lookup (key node) (fromList key nodes) with
    | none => exact False.elim (present found)
    | some winner =>
        have original := fromList_origin key nodes (key node) winner found
        have same := faithful winner original.1 node member original.2
        subst winner
        exact List.mem_map.mpr ⟨(key node, node), lookup_mem _ _ _ found, rfl⟩

/-- The actual ascending map readback is strictly ordered by resident key. -/
theorem elems_ordered (key : Node → Int) (nodes : List Node) :
    (elems key nodes).Pairwise (fun left right => key left < key right) := by
  apply List.pairwise_map.mpr
  apply (fromList_ascending key nodes).imp_of_mem
  intro left right leftIn rightIn before
  have first := (fromList_origin key nodes left.1 left.2
    (lookup_of_mem left.1 _ left.2 (fromList_ascending key nodes) leftIn)).2
  have second := (fromList_origin key nodes right.1 right.2
    (lookup_of_mem right.1 _ right.2 (fromList_ascending key nodes) rightIn)).2
  simpa only [first, second] using before

/-- Strict ascending key order excludes repeated values. -/
theorem elems_nodup (key : Node → Int) (nodes : List Node) : (elems key nodes).Nodup := by
  exact (elems_ordered key nodes).imp (fun before same => by cases same; exact Int.lt_irrefl _ before)

private theorem eraseDups_nodup [DecidableEq Node] (nodes : List Node) : nodes.eraseDups.Nodup := by
  cases nodes with
  | nil => simp
  | cons node nodes =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, eraseDups_nodup (nodes.filter (fun other => !other == node))⟩
      simp [List.mem_eraseDups]
termination_by nodes.length
decreasing_by
  have bound := List.length_filter_le (fun other => !other == node) nodes
  simp only [List.length_cons]
  omega

/-- Literal insertion and ascending elems give the exact earlier canonical node sequence. -/
theorem elems_exact [DecidableEq Node] (key : Node → Int) (nodes : List Node) (faithful : FaithfulOn key nodes) :
    elems key nodes = nodes.eraseDups.mergeSort (fun left right => decide (key left ≤ key right)) := by
  let sorted := nodes.eraseDups.mergeSort (fun left right => decide (key left ≤ key right))
  have members : ∀ node, node ∈ sorted ↔ node ∈ nodes := fun node => List.mem_mergeSort.trans List.mem_eraseDups
  have unique : sorted.Nodup := (List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup nodes)
  have permutation : (elems key nodes).Perm sorted :=
    (List.perm_ext_iff_of_nodup (elems_nodup key nodes) unique).mpr
      (fun node => (mem_elems key nodes faithful node).trans (members node).symm)
  have ordered : sorted.Pairwise (fun left right => key left ≤ key right) := by
    have result := List.pairwise_mergeSort (le := fun left right : Node => decide (key left ≤ key right))
      (by intro left middle right first second; simp only [decide_eq_true_eq] at *; omega)
      (by intro left right; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) nodes.eraseDups
    simpa only [sorted, decide_eq_true_eq] using result
  exact permutation.eq_of_pairwise
    (fun left right leftIn rightIn first second => faithful left ((mem_elems key nodes faithful left).mp leftIn)
      right ((members right).mp rightIn) (by omega))
    ((elems_ordered key nodes).imp (fun before => Int.le_of_lt before)) ordered

/-- The source empty-node shortcut precedes every map demand. -/
def conjunction [DecidableEq Node] (empty : Node) (key : Node → Int) (nodes : List Node) : List Node :=
  if empty ∈ nodes then [empty] else elems key nodes

/-- Closed faithful resident keys discharge the canonical conjunction sequence adapter. -/
theorem conjunction_exact [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (faithful : SourceCurrentConjunctionEmptinessTable.KeyFaithful empty key closed)
    (nodes : List Node) (allClosed : nodes.all closed = true) :
    conjunction empty key nodes = SourceCurrentConjunctionEmptinessRows.conjunction empty key nodes := by
  by_cases impossible : empty ∈ nodes
  · simp [conjunction, SourceCurrentConjunctionEmptinessRows.conjunction, impossible]
  · simp only [conjunction, SourceCurrentConjunctionEmptinessRows.conjunction, impossible, ite_false]
    apply elems_exact
    intro left leftIn right rightIn same
    exact faithful left right (fun equal => impossible (equal ▸ leftIn)) (fun equal => impossible (equal ▸ rightIn))
      ((List.all_eq_true).mp allClosed left leftIn) ((List.all_eq_true).mp allClosed right rightIn) same

/-- The literal source map preserves exactly common-term acceptance on faithful closed inputs. -/
theorem conjunction_accepts [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (faithful : SourceCurrentConjunctionEmptinessTable.KeyFaithful empty key closed)
    (nodes : List Node) (allClosed : nodes.all closed = true)
    (meaning : Node → Language.Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (term : Language.Term Symbol) :
    SourceCurrentConjunctionEmptinessRows.Accepts meaning (conjunction empty key nodes) term ↔
      SourceCurrentConjunctionEmptinessRows.Accepts meaning nodes term := by
  rw [conjunction_exact empty key closed faithful nodes allClosed]
  exact SourceCurrentConjunctionEmptinessRows.conjunction_exact empty key meaning emptyFalse nodes term

end MicroCFTA.SourceCurrentConjunctionMap
