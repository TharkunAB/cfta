import MicroCFTA.SymbolicSelection
import Init.Data.Order.Ord

/-!
# Ordered canonical graph classes

The source keys each node by its old class and its sorted edge rows. It
numbers the distinct keys in ascending order. The finite domain contains
all child identities. Its enumeration order does not enter a row key.
-/
namespace MicroCFTA.CanonicalClasses
open Std
attribute [local instance] lexOrd

/-- A finite closed identity domain with complete outgoing rows. -/
structure Graph (Node Key : Type) where
  nodes : List Node
  complete : ∀ node, node ∈ nodes
  distinct : nodes.Nodup
  rows : Node → List (Key × List Node)

/-- Source set readback uses structural duplicate removal and ascending order. -/
def sortedSet [DecidableEq α] [Ord α] (items : List α) : List α :=
  items.eraseDups.mergeSort fun a b => (compare a b).isLE

/-- Sorted set membership is exactly source key membership. -/
theorem mem_sortedSet [DecidableEq α] [Ord α] (items : List α) (item : α) :
    item ∈ sortedSet items ↔ item ∈ items := by simp [sortedSet]

/-- Ascending set readback has no repeated key. -/
theorem sortedSet_nodup [DecidableEq α] [Ord α] (items : List α) : (sortedSet items).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (SymbolicDriver.eraseDups_nodup items)

/-- Ascending set readback is ordered by the source comparison. -/
theorem sortedSet_ordered [DecidableEq α] [Ord α] [TransOrd α] (items : List α) :
    (sortedSet items).Pairwise (fun a b => (compare a b).isLE = true) := by
  apply List.pairwise_mergeSort
  · intro a b c ab bc
    exact TransOrd.isLE_trans ab bc
  · intro a b
    have swap := OrientedOrd.eq_swap (a := a) (b := b)
    cases first : compare a b <;> cases second : compare b a <;> simp_all

/-- Set numbering depends on keys alone, not on their input enumeration. -/
theorem sortedSet_ext [DecidableEq α] [Ord α] [TransOrd α] [LawfulEqOrd α]
    (first second : List α) (same : ∀ item, item ∈ first ↔ item ∈ second) :
    sortedSet first = sortedSet second := by
  have antisymm : ∀ a b : α, (compare a b).isLE = true → (compare b a).isLE = true → a = b := by
    intro a b ab ba
    apply LawfulEqOrd.eq_of_compare
    exact Ordering.eq_eq_of_isLE_of_isLE_swap ab (by simpa only [← OrientedOrd.eq_swap] using ba)
  apply List.Perm.eq_of_pairwise (fun a b _ _ => antisymm a b)
    (sortedSet_ordered first) (sortedSet_ordered second)
  exact (List.perm_ext_iff_of_nodup (sortedSet_nodup first) (sortedSet_nodup second)).mpr
    (fun item => by simpa only [mem_sortedSet] using same item)

/-- Set cardinality is bounded by the source list length. -/
theorem sortedSet_length [DecidableEq α] [Ord α] (items : List α) :
    (sortedSet items).length ≤ items.length :=
  (sortedSet_nodup items).length_le_of_subset (fun _ member => (mem_sortedSet items _).mp member)

/-- A duplicate-free subset of equal length is a permutation, without a second distinctness premise. -/
theorem perm_of_nodup_subset_length [DecidableEq α] (first second : List α)
    (distinct : first.Nodup) (included : first ⊆ second) (lengthEq : first.length = second.length) :
    first.Perm second := by
  induction first generalizing second with
  | nil => have empty : second = [] := List.length_eq_zero_iff.mp lengthEq.symm; subst second; exact .nil
  | cons item rest ih =>
      have pair := List.nodup_cons.mp distinct
      have present : item ∈ second := included (by simp)
      have restIncluded : rest ⊆ second.erase item := by
        intro other member
        have different : other ≠ item := fun same => pair.1 (same ▸ member)
        exact (List.mem_erase_of_ne different).mpr (included (by simp [member]))
      have restLength : rest.length = (second.erase item).length := by
        have erased := (List.perm_cons_erase present).length_eq
        simp only [List.length_cons] at lengthEq erased
        omega
      exact (List.Perm.cons item (ih (second.erase item) pair.2 restIncluded restLength)).trans (List.perm_cons_erase present).symm

/-- A node key keeps its old class before its sorted edge keys and ordered child classes. -/
def nodeKey [Ord Key] (graph : Graph Node Key) (classes : Node → Nat) (node : Node) :
    Nat × List (Key × List Nat) :=
  (classes node, ((graph.rows node).map fun edge => (edge.1, edge.2.map classes)).mergeSort
    fun a b => (compare a b).isLE)

/-- Source distinct keys in their numbering order. -/
def keys [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat) :=
  sortedSet (graph.nodes.map (nodeKey graph classes))

/-- One source refinement round assigns the zero-based ascending key index. -/
def step [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat) (node : Node) : Nat :=
  (keys graph classes).idxOf (nodeKey graph classes node)

/-- Every domain node has a numbered key. -/
theorem key_member [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat) (node : Node) :
    nodeKey graph classes node ∈ keys graph classes :=
  (mem_sortedSet _ _).mpr (List.mem_map.mpr ⟨node, graph.complete node, rfl⟩)

/-- Every numbered key comes from a domain node. -/
theorem key_origin [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat)
    (key : Nat × List (Key × List Nat)) (member : key ∈ keys graph classes) :
    ∃ node, nodeKey graph classes node = key := by
  obtain ⟨node, _, same⟩ := List.mem_map.mp ((mem_sortedSet _ key).mp member)
  exact ⟨node, same⟩

/-- Number lookup recovers the complete structural key. -/
theorem step_key [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat) (node : Node) :
    (keys graph classes)[step graph classes node]? = some (nodeKey graph classes node) := by
  have bounded := List.idxOf_lt_length_of_mem (key_member graph classes node)
  simp [step, List.getElem?_eq_getElem bounded]

/-- One round identifies exactly equal complete row keys. -/
theorem step_equal_iff [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat)
    (first second : Node) : step graph classes first = step graph classes second ↔
      nodeKey graph classes first = nodeKey graph classes second := by
  constructor
  · intro same
    have a := step_key graph classes first
    have b := step_key graph classes second
    rw [same, b] at a
    exact (Option.some.inj a).symm
  · intro same
    simp only [step, same]

/-- Keeping the old class in the key prevents every possible class merge. -/
theorem no_merge [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat)
    (first second : Node) (same : step graph classes first = step graph classes second) : classes first = classes second :=
  congrArg Prod.fst ((step_equal_iff graph classes first second).mp same)

/-- A class table uses every integer below its count and no other integer. -/
def Dense (classes : Node → Nat) (count : Nat) : Prop :=
  (∀ node, classes node < count) ∧ ∀ rank, rank < count → ∃ node, classes node = rank

/-- A distinct list's index lookup recovers every in-range position. -/
theorem idxOf_get [BEq α] [LawfulBEq α] (items : List α) (distinct : items.Nodup) (rank : Nat) (within : rank < items.length) :
    items.idxOf items[rank] = rank := by
  have member : items[rank] ∈ items := List.getElem_mem within
  have bound := List.idxOf_lt_length_of_mem member
  exact distinct.eq_of_getElem_eq bound within (List.getElem_idxOf bound)

/-- Source ordered numbering is dense at the number of distinct keys. -/
theorem step_dense [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat) :
    Dense (step graph classes) (keys graph classes).length := by
  constructor
  · intro node
    exact List.idxOf_lt_length_of_mem (key_member graph classes node)
  · intro rank within
    obtain ⟨node, same⟩ := key_origin graph classes _ (List.getElem_mem within)
    refine ⟨node, ?_⟩
    unfold step
    rw [same]
    exact idxOf_get _ (sortedSet_nodup _) rank within

/-- Every old class occurs as the first component of a new key. -/
theorem old_range_subset [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat)
    (count : Nat) (dense : Dense classes count) :
    List.range count ⊆ (keys graph classes).map Prod.fst := by
  intro rank member
  obtain ⟨node, same⟩ := dense.2 rank (List.mem_range.mp member)
  exact List.mem_map.mpr ⟨nodeKey graph classes node, key_member graph classes node, same⟩

/-- No source round decreases the number of classes. -/
theorem count_monotone [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat)
    (count : Nat) (dense : Dense classes count) : count ≤ (keys graph classes).length := by
  have bounded := (List.nodup_range (n := count)).length_le_of_subset (old_range_subset graph classes count dense)
  simpa using bounded

/-- Every round has at most one class per domain node. -/
theorem count_bound [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat) :
    (keys graph classes).length ≤ graph.nodes.length := by
  simpa [keys] using sortedSet_length (graph.nodes.map (nodeKey graph classes))

/-- A non-stopping round strictly increases the finite class count. -/
theorem count_progress [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat)
    (count : Nat) (dense : Dense classes count) (different : (keys graph classes).length ≠ count) :
    count < (keys graph classes).length := by
  have monotone := count_monotone graph classes count dense
  omega

/-- A duplicate-free mapped list makes its map injective on the original list. -/
theorem map_injective_of_nodup (f : α → β) (items : List α) (distinct : (items.map f).Nodup)
    (first second : α) (a : first ∈ items) (b : second ∈ items) (same : f first = f second) : first = second := by
  induction items with
  | nil => cases a
  | cons head rest ih =>
      have pair := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp a with rfl | firstRest
      · rcases List.mem_cons.mp b with rfl | secondRest
        · rfl
        · exact False.elim (pair.1 (List.mem_map.mpr ⟨second, secondRest, same.symm⟩))
      · rcases List.mem_cons.mp b with rfl | secondRest
        · exact False.elim (pair.1 (List.mem_map.mpr ⟨first, firstRest, same⟩))
        · exact ih pair.2 firstRest secondRest

/-- Equal class counts mean that no old class split during this source round. -/
theorem count_equal_partition [DecidableEq Key] [Ord Key] (graph : Graph Node Key) (classes : Node → Nat)
    (count : Nat) (dense : Dense classes count) (sameCount : (keys graph classes).length = count)
    (first second : Node) : step graph classes first = step graph classes second ↔ classes first = classes second := by
  constructor
  · exact no_merge graph classes first second
  · intro same
    have perm := perm_of_nodup_subset_length (List.range count) ((keys graph classes).map Prod.fst)
      (List.nodup_range (n := count)) (old_range_subset graph classes count dense) (by simp [sameCount])
    have distinct := perm.nodup_iff.mp (List.nodup_range (n := count))
    apply (step_equal_iff graph classes first second).mpr
    exact map_injective_of_nodup Prod.fst _ distinct _ _
      (key_member graph classes first) (key_member graph classes second) same

/-- Lexicographic row-key order always respects the first, old-class component. -/
theorem key_first_le [Ord Detail] (first second : Nat × Detail)
    (ordered : (compare first second).isLE = true) : first.1 ≤ second.1 := by
  by_cases conclusion : first.1 ≤ second.1
  · exact conclusion
  apply False.elim
  have reverse : second.1 < first.1 := by omega
  have different := Nat.compare_eq_gt.mpr reverse
  change ((compare first.1 second.1).then (compare first.2 second.2)).isLE = true at ordered
  simp [different] at ordered

/-- Once two nodes separate, all later rounds retain their relative class order. -/
theorem step_preserves_order [DecidableEq Key] [Ord Key] [TransOrd Key]
    (graph : Graph Node Key) (classes : Node → Nat) (first second : Node)
    (before : classes first < classes second) : step graph classes first < step graph classes second := by
  have firstBound := (step_dense graph classes).1 first
  have secondBound := (step_dense graph classes).1 second
  by_cases conclusion : step graph classes first < step graph classes second
  · exact conclusion
  apply False.elim
  have notSame : step graph classes first ≠ step graph classes second := by
    intro same
    have oldSame := no_merge graph classes first second same
    omega
  have reverse : step graph classes second < step graph classes first := by omega
  have ordered := (sortedSet_ordered (graph.nodes.map (nodeKey graph classes))).rel_getElem_of_lt
    secondBound firstBound reverse
  have lower := key_first_le _ _ ordered
  have reverseOld : classes second ≤ classes first := by
    simpa only [step, List.getElem_idxOf, nodeKey] using lower
  omega

/-- At unchanged count, the old class components occur in exact ascending range order. -/
theorem stopped_projection [DecidableEq Key] [Ord Key] [TransOrd Key]
    (graph : Graph Node Key) (classes : Node → Nat) (count : Nat) (dense : Dense classes count)
    (sameCount : (keys graph classes).length = count) :
    (keys graph classes).map Prod.fst = List.range count := by
  have perm := perm_of_nodup_subset_length (List.range count) ((keys graph classes).map Prod.fst)
    (List.nodup_range (n := count)) (old_range_subset graph classes count dense) (by simp [sameCount])
  have oldOrdered : ((keys graph classes).map Prod.fst).Pairwise (· ≤ ·) := by
    apply List.pairwise_map.mpr
    exact (sortedSet_ordered (graph.nodes.map (nodeKey graph classes))).imp (fun ordered => key_first_le _ _ ordered)
  have rangeOrdered : (List.range count).Pairwise (· ≤ ·) :=
    List.pairwise_lt_range.imp (fun before => Nat.le_of_lt before)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ => Nat.le_antisymm) oldOrdered rangeOrdered perm.symm

/-- The source stopping test gives an exact numeric fixed point, not only the same partition. -/
theorem count_equal_fixed [DecidableEq Key] [Ord Key] [TransOrd Key]
    (graph : Graph Node Key) (classes : Node → Nat) (count : Nat) (dense : Dense classes count)
    (sameCount : (keys graph classes).length = count) : step graph classes = classes := by
  funext node
  have projection := stopped_projection graph classes count dense sameCount
  have bounded : step graph classes node < count := by simpa [sameCount] using (step_dense graph classes).1 node
  have read : ((keys graph classes).map Prod.fst)[step graph classes node]? = some (classes node) := by
    simp only [List.getElem?_map, step_key, Option.map_some, nodeKey]
  rw [projection] at read
  simpa [bounded] using read

/-- The bounded port performs precisely the source count comparison and next-class recurrence. -/
def refine [DecidableEq Key] [Ord Key] (graph : Graph Node Key) :
    Nat → (Node → Nat) → Nat → Option (Node → Nat)
  | 0, _, _ => none
  | fuel + 1, classes, count =>
      let count' := (keys graph classes).length
      let classes' := step graph classes
      if count' = count then some classes' else refine graph fuel classes' count'

/-- At most one plus the number of still-possible splits is enough fuel. -/
theorem refine_terminates [DecidableEq Key] [Ord Key] (graph : Graph Node Key)
    (fuel : Nat) (classes : Node → Nat) (count : Nat) (dense : Dense classes count)
    (enough : graph.nodes.length - count < fuel) : ∃ result, refine graph fuel classes count = some result := by
  induction fuel generalizing classes count with
  | zero => omega
  | succ fuel ih =>
      by_cases stable : (keys graph classes).length = count
      · exact ⟨step graph classes, by simp [refine, stable]⟩
      · have progress := count_progress graph classes count dense stable
        have bounded := count_bound graph classes
        have enough' : graph.nodes.length - (keys graph classes).length < fuel := by omega
        obtain ⟨result, found⟩ := ih (step graph classes) (keys graph classes).length (step_dense graph classes) enough'
        exact ⟨result, by simp [refine, stable, found]⟩

/-- Every successful source loop result is an exact stable numeric table. -/
theorem refine_fixed [DecidableEq Key] [Ord Key] [TransOrd Key] (graph : Graph Node Key)
    (fuel : Nat) (classes : Node → Nat) (count : Nat) (dense : Dense classes count)
    (result : Node → Nat) (found : refine graph fuel classes count = some result) : step graph result = result := by
  induction fuel generalizing classes count with
  | zero => cases found
  | succ fuel ih =>
      simp only [refine] at found
      split at found
      next same =>
        have fixed := count_equal_fixed graph classes count dense same
        have resultEq : step graph classes = result := Option.some.inj found
        rw [fixed] at resultEq
        subst result
        exact fixed
      next different => exact ih _ _ (step_dense graph classes) found

/-- Successful rounds also retain every previously established class order. -/
theorem refine_preserves_order [DecidableEq Key] [Ord Key] [TransOrd Key] (graph : Graph Node Key)
    (fuel : Nat) (classes result : Node → Nat) (count : Nat) (found : refine graph fuel classes count = some result)
    (first second : Node) (before : classes first < classes second) : result first < result second := by
  induction fuel generalizing classes count with
  | zero => cases found
  | succ fuel ih =>
      have next := step_preserves_order graph classes first second before
      simp only [refine] at found
      split at found
      next => cases found; exact next
      next => exact ih _ _ found next

/-- Initial class zero has the exact source count, including an empty graph. -/
theorem initial_dense (graph : Graph Node Key) : Dense (fun _ : Node => 0) (min 1 graph.nodes.length) := by
  cases shape : graph.nodes with
  | nil =>
      constructor
      · intro node
        have member := graph.complete node
        simp [shape] at member
      · intro rank within
        simp at within
  | cons first rest =>
      constructor
      · intro node; simp
      · intro rank within
        have zero : rank = 0 := by simpa [shape] using within
        exact ⟨first, zero.symm⟩

/-- The executable canonical loop has a proved finite budget. -/
def canonical [DecidableEq Key] [Ord Key] (graph : Graph Node Key) : Option (Node → Nat) :=
  refine graph (graph.nodes.length + 1) (fun _ => 0) (min 1 graph.nodes.length)

/-- Every finite closed graph completes the actual class-refinement loop. -/
theorem canonical_terminates [DecidableEq Key] [Ord Key] (graph : Graph Node Key) :
    ∃ classes, canonical graph = some classes :=
  refine_terminates graph _ _ _ (initial_dense graph) (by omega)

/-- Every completed canonical table is an exact fixed point of sorted row refinement. -/
theorem canonical_fixed [DecidableEq Key] [Ord Key] [TransOrd Key] (graph : Graph Node Key)
    (classes : Node → Nat) (found : canonical graph = some classes) : step graph classes = classes :=
  refine_fixed graph _ _ _ (initial_dense graph) classes found


/-- Sorting a row list removes dependence on its edge enumeration order. -/
theorem sort_perm_equal [Ord α] [TransOrd α] [LawfulEqOrd α]
    (first second : List α) (perm : first.Perm second) :
    first.mergeSort (fun a b => (compare a b).isLE) = second.mergeSort (fun a b => (compare a b).isLE) := by
  have ordered (items : List α) :
      (items.mergeSort (fun a b => (compare a b).isLE)).Pairwise (fun a b => (compare a b).isLE = true) := by
    apply List.pairwise_mergeSort
    · intro a b c ab bc; exact TransOrd.isLE_trans ab bc
    · intro a b
      have swap := OrientedOrd.eq_swap (a := a) (b := b)
      cases first : compare a b <;> cases second : compare b a <;> simp_all
  have antisymm : ∀ a b : α, (compare a b).isLE = true → (compare b a).isLE = true → a = b := by
    intro a b ab ba
    apply LawfulEqOrd.eq_of_compare
    exact Ordering.eq_eq_of_isLE_of_isLE_swap ab (by simpa only [← OrientedOrd.eq_swap] using ba)
  exact List.Perm.eq_of_pairwise (fun a b _ _ => antisymm a b) (ordered first) (ordered second)
    ((List.mergeSort_perm _ _).trans (perm.trans (List.mergeSort_perm _ _).symm))

/-- A change of identities preserves edge keys and ordered child lists. Edge rows may be permuted. -/
structure Renaming (first : Graph Node Key) (second : Graph Other Key) where
  forward : Node → Other
  backward : Other → Node
  left_inverse : ∀ node, backward (forward node) = node
  right_inverse : ∀ node, forward (backward node) = node
  rows : ∀ node, (second.rows (forward node)).Perm
    ((first.rows node).map fun edge => (edge.1, edge.2.map forward))

/-- Class transport changes only the identity used to read a class. -/
def transport {first : Graph Node Key} {second : Graph Other Key}
    (rename : Renaming first second) (classes : Node → Nat) : Other → Nat :=
  fun node => classes (rename.backward node)

/-- Node enumeration sizes agree under a structural identity renaming. -/
theorem renamed_length (first : Graph Node Key) (second : Graph Other Key) (rename : Renaming first second) :
    first.nodes.length = second.nodes.length := by
  have distinct : (first.nodes.map rename.forward).Nodup :=
    first.distinct.map _ (fun a b different same => different (by
      have eq := congrArg rename.backward same
      simpa only [rename.left_inverse] using eq))
  have perm : (first.nodes.map rename.forward).Perm second.nodes := by
    apply (List.perm_ext_iff_of_nodup distinct second.distinct).mpr
    intro node
    constructor
    · intro _; exact second.complete node
    · intro _
      exact List.mem_map.mpr ⟨rename.backward node, first.complete _, rename.right_inverse node⟩
  simpa using perm.length_eq

/-- Sorted row keys commute with identity renaming and arbitrary edge-row permutations. -/
theorem nodeKey_rename [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (first : Graph Node Key) (second : Graph Other Key) (rename : Renaming first second)
    (classes : Node → Nat) (node : Node) :
    nodeKey second (transport rename classes) (rename.forward node) = nodeKey first classes node := by
  apply Prod.ext
  · simp [nodeKey, transport, rename.left_inverse]
  · apply sort_perm_equal
    have perm := (rename.rows node).map (fun edge => (edge.1, edge.2.map (transport rename classes)))
    simpa only [List.map_map, Function.comp_def, transport, rename.left_inverse] using perm

/-- The ascending distinct key list is independent of identities and domain enumeration order. -/
theorem keys_rename [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (first : Graph Node Key) (second : Graph Other Key) (rename : Renaming first second)
    (classes : Node → Nat) : keys second (transport rename classes) = keys first classes := by
  apply sortedSet_ext
  intro key
  constructor
  · rintro member
    obtain ⟨node, _, same⟩ := List.mem_map.mp member
    refine List.mem_map.mpr ⟨rename.backward node, first.complete _, ?_⟩
    have keySame := nodeKey_rename first second rename classes (rename.backward node)
    rw [rename.right_inverse] at keySame
    exact keySame.symm.trans same
  · rintro member
    obtain ⟨node, _, same⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨rename.forward node, second.complete _,
      (nodeKey_rename first second rename classes node).trans same⟩

/-- One exact numeric refinement round commutes with identity renaming. -/
theorem step_rename [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (first : Graph Node Key) (second : Graph Other Key) (rename : Renaming first second)
    (classes : Node → Nat) : step second (transport rename classes) = transport rename (step first classes) := by
  funext node
  have keySame := nodeKey_rename first second rename classes (rename.backward node)
  rw [rename.right_inverse] at keySame
  simp only [step, keys_rename first second rename classes, keySame, transport]

/-- The complete source loop commutes with structural identity renaming. -/
theorem refine_rename [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (first : Graph Node Key) (second : Graph Other Key) (rename : Renaming first second)
    (fuel : Nat) (classes : Node → Nat) (count : Nat) :
    refine second fuel (transport rename classes) count =
      (refine first fuel classes count).map (transport rename) := by
  induction fuel generalizing classes count with
  | zero => rfl
  | succ fuel ih =>
      simp only [refine, keys_rename first second rename classes, step_rename first second rename classes]
      split
      · rfl
      · exact ih _ _

/-- Canonical numeric classes, and therefore their rank order, do not depend on interning identities. -/
theorem canonical_rename [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (first : Graph Node Key) (second : Graph Other Key) (rename : Renaming first second) :
    canonical second = (canonical first).map (transport rename) := by
  unfold canonical
  rw [← renamed_length first second rename]
  exact refine_rename first second rename _ (fun _ => 0) _

/-- Equal final classes have exactly the same sorted rows of keys and final child classes. -/
theorem final_rows_exact [DecidableEq Key] [Ord Key] [TransOrd Key]
    (graph : Graph Node Key) (classes : Node → Nat) (found : canonical graph = some classes)
    (first second : Node) (same : classes first = classes second) :
    (nodeKey graph classes first).2 = (nodeKey graph classes second).2 := by
  have fixed := canonical_fixed graph classes found
  have keySame := (step_equal_iff graph classes first second).mp (by simpa only [fixed] using same)
  exact congrArg Prod.snd keySame


/-- The compact edge ordering key contains the supplied key and each ordered child class. -/
def edgeKey (classes : Node → Nat) (edge : Key × List Node) : Key × List Nat :=
  (edge.1, edge.2.map classes)

/-- Final child-class edge keys are identical after a structural identity renaming. -/
theorem final_edge_key_rename [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (first : Graph Node Key) (second : Graph Other Key) (rename : Renaming first second)
    (firstClasses : Node → Nat) (secondClasses : Other → Nat)
    (firstDone : canonical first = some firstClasses) (secondDone : canonical second = some secondClasses)
    (edge : Key × List Node) :
    edgeKey secondClasses (edge.1, edge.2.map rename.forward) = edgeKey firstClasses edge := by
  have same := canonical_rename first second rename
  rw [firstDone, secondDone] at same
  have tableSame := Option.some.inj same
  rw [tableSame]
  simp [edgeKey, transport, List.map_map, Function.comp_def, rename.left_inverse]

/-- The final source row ordering key sequence is invariant under identities and edge permutations. -/
theorem final_sorted_rows_rename [DecidableEq Key] [Ord Key] [TransOrd Key] [LawfulEqOrd Key]
    (first : Graph Node Key) (second : Graph Other Key) (rename : Renaming first second)
    (firstClasses : Node → Nat) (secondClasses : Other → Nat)
    (firstDone : canonical first = some firstClasses) (secondDone : canonical second = some secondClasses)
    (node : Node) :
    ((second.rows (rename.forward node)).map (edgeKey secondClasses)).mergeSort (fun a b => (compare a b).isLE) =
      ((first.rows node).map (edgeKey firstClasses)).mergeSort (fun a b => (compare a b).isLE) := by
  have same := canonical_rename first second rename
  rw [firstDone, secondDone] at same
  rw [Option.some.inj same]
  exact congrArg Prod.snd (nodeKey_rename first second rename firstClasses node)

/-- The result keeps every prior separation throughout later executed rounds. -/
theorem no_merge_after_refine [DecidableEq Key] [Ord Key] (graph : Graph Node Key)
    (fuel : Nat) (classes result : Node → Nat) (count : Nat) (found : refine graph fuel classes count = some result)
    (first second : Node) (same : result first = result second) : classes first = classes second := by
  induction fuel generalizing classes count with
  | zero => cases found
  | succ fuel ih =>
      simp only [refine] at found
      split at found
      next => cases found; exact no_merge graph classes first second same
      next => exact no_merge graph classes first second (ih _ _ found)

/-- A three-state graph needs a second split to distinguish its two unary rows. -/
def delayedGraph : Graph (Fin 3) Nat where
  nodes := List.finRange 3
  complete := by intro node; simp
  distinct := List.nodup_finRange 3
  rows node := if node = 0 then [(0, [])] else if node = 1 then [(1, [0])] else [(1, [1])]

/-- The loop continues while counts grow and stops only after the final unchanged round. -/
theorem delayed_example :
    refine delayedGraph 2 (fun _ => 0) 1 = none ∧
    (canonical delayedGraph).map (fun classes => [classes 0, classes 1, classes 2]) = some [0, 1, 2] := by
  cbv

/-- Cyclic rows remain finite inputs to partition refinement. -/
def cyclicGraph : Graph Bool Nat where
  nodes := [false, true]
  complete := by intro node; cases node <;> simp
  distinct := by decide
  rows node := if node then [(1, [false])] else [(0, [false])]

/-- Swapping node identities changes neither canonical content nor its numeric order. -/
def swappedGraph : Graph Bool Nat where
  nodes := [true, false]
  complete := by intro node; cases node <;> simp
  distinct := by decide
  rows node := if node then [(0, [true])] else [(1, [true])]

/-- The cyclic identity swap satisfies the complete structural source correspondence. -/
def cyclicSwap : Renaming cyclicGraph swappedGraph where
  forward := Bool.not
  backward := Bool.not
  left_inverse := by intro node; simp
  right_inverse := by intro node; simp
  rows := by intro node; cases node <;> simp [cyclicGraph, swappedGraph]

/-- Concrete cyclic canonical numbering follows content after the identity swap. -/
theorem cyclic_rename_example :
    (canonical cyclicGraph).map (fun classes => (classes false, classes true)) = some (0, 1) ∧
    (canonical swappedGraph).map (fun classes => (classes false, classes true)) = some (1, 0) := by
  cbv


/-- An empty source graph has no identity and no outgoing row. -/
def emptyGraph : Graph Empty Nat where
  nodes := []
  complete := by intro node; cases node
  distinct := by simp
  rows := fun node => nomatch node

/-- The empty graph stops at the first unchanged zero-count round. -/
theorem empty_example : (canonical emptyGraph).isSome = true := by cbv


end MicroCFTA.CanonicalClasses
