import MicroCFTA.FiniteRowIntersection
import MicroCFTA.RecursiveReductionSourceOrder

/-!
# Finite structural progress for source residual alternatives

The finite row inventory comes from subsets of the original outer guard
atoms. Every row uses the exact source structural order and conjunction.
This covers alternative residual rows at one fixed leaf symbol. Nested
child-node products and path edits require an additional composition proof.
-/
namespace MicroCFTA.SourceLeafRowProgress
open SourceGuards FullSyntax GuardConjunction
open FiniteRowIntersection

/-- Enumerate all sublists in input order, including the empty choice. -/
def subsets : List Item → List (List Item)
  | [] => [[]]
  | head :: tail => subsets tail ++ (subsets tail).map (head :: ·)

/-- The generated inventory has an explicit finite size before duplicate removal. -/
theorem subsets_length (items : List Item) : (subsets items).length = 2 ^ items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [subsets, ih, Nat.pow_succ, Nat.mul_two]

/-- Every enumerated sublist uses only original elements. -/
theorem subsets_subset (items selected : List Item) (present : selected ∈ subsets items) :
    ∀ item ∈ selected, item ∈ items := by
  induction items generalizing selected with
  | nil => simp [subsets] at present; subst selected; simp
  | cons head tail ih =>
      simp only [subsets, List.mem_append, List.mem_map] at present
      rcases present with present | ⟨rest, present, rfl⟩
      · exact fun item member => List.mem_cons_of_mem head (ih selected present item member)
      · intro item member
        rcases List.mem_cons.mp member with rfl | member
        · simp
        · exact List.mem_cons_of_mem head (ih rest present item member)

/-- Filtering the original list always produces an enumerated choice. -/
theorem filter_mem_subsets (items : List Item) (select : Item → Bool) : items.filter select ∈ subsets items := by
  induction items with
  | nil => simp [subsets]
  | cons head tail ih =>
      cases selected : select head <;> simp [subsets, selected, ih]

/-- Initial source guards supply a finite, already flattened atom inventory. -/
def basis (initial : List (Guard Formula)) : List (Guard Formula) := initial.flatMap atoms

/-- Every atom in the generated inventory is indivisible by outer flattening. -/
theorem basis_irreducible (initial : List (Guard Formula)) (atom : Guard Formula) (present : atom ∈ basis initial) :
    atoms atom = [atom] := by
  obtain ⟨guard, member, found⟩ := List.mem_flatMap.mp present
  exact atoms_irreducible guard atom found

/-- A canonical residual contains only atoms from the original source guards. -/
def Row (initial : List (Guard Formula)) :=
  {guard : Guard Formula // normalize GuardStructuralOrder.le guard = guard ∧
    ∀ atom ∈ atoms guard, atom ∈ basis initial}

/-- Canonical source conjunction stays inside the generated finite atom inventory. -/
def join (initial : List (Guard Formula)) (first second : Row initial) : Row initial :=
  ⟨merge GuardStructuralOrder.le first.val second.val,
    normalize_idempotent GuardStructuralOrder.le GuardStructuralOrder.le_trans
      GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm _,
    fun atom present => (merge_mem _ _ _ _).mp present |>.elim (first.property.2 atom) (second.property.2 atom)⟩

/-- The source comparator and normalizer derive all individual-row conjunction laws. -/
def algebra (initial : List (Guard Formula)) : Conjunction (Row initial) where
  join := join initial
  assoc := fun first second third => Subtype.ext (merge_associative GuardStructuralOrder.le
    GuardStructuralOrder.le_trans GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm _ _ _)
  comm := fun first second => Subtype.ext (merge_commutative GuardStructuralOrder.le
    GuardStructuralOrder.le_trans GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm _ _)
  idem := fun row => Subtype.ext (by
    change merge GuardStructuralOrder.le row.val row.val = row.val
    simpa only [row.property.1] using merge_normalized_self GuardStructuralOrder.le GuardStructuralOrder.le_trans
      GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm row.val)

/-- Build one actual canonical guard from an enumerated atom subset. -/
def fromSubset (initial : List (Guard Formula)) (selected : List (Guard Formula))
    (present : selected ∈ subsets (basis initial)) : Row initial :=
  ⟨normalize GuardStructuralOrder.le (conjoin selected),
    normalize_idempotent GuardStructuralOrder.le GuardStructuralOrder.le_trans
      GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm _, by
      intro atom member
      rw [atoms_normalize, canonical_mem,
        atoms_conjoin selected (fun atom member => basis_irreducible initial atom (subsets_subset _ _ present atom member))] at member
      exact subsets_subset _ _ present atom member⟩

/-- Enumerate the finite source row inventory without assuming a size bound. -/
def inventory (initial : List (Guard Formula)) : List (Row initial) :=
  (subsets (basis initial)).attach.map (fun selected => fromSubset initial selected.val selected.property)

/-- Every residual over the original atoms occurs in the generated inventory. -/
theorem inventory_complete (initial : List (Guard Formula)) (row : Row initial) : row ∈ inventory initial := by
  let selected := (basis initial).filter (fun atom => atom ∈ atoms row.val)
  have present : selected ∈ subsets (basis initial) := filter_mem_subsets _ _
  apply List.mem_map.mpr
  refine ⟨⟨selected, present⟩, List.mem_attach _ _, ?_⟩
  apply Subtype.ext
  change normalize GuardStructuralOrder.le (conjoin selected) = row.val
  rw [← row.property.1]
  apply normalize_eq GuardStructuralOrder.le GuardStructuralOrder.le_trans
    GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm
  intro atom
  rw [atoms_conjoin selected (fun atom member => basis_irreducible initial atom (List.mem_filter.mp member).1)]
  simp only [selected, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun member => member.2, fun member => ⟨row.property.2 atom member, member⟩⟩

/-- The complete source inventory has at most one slot per original atom subset. -/
theorem inventory_length (initial : List (Guard Formula)) :
    (inventory initial).length = 2 ^ (basis initial).length := by
  simp [inventory, subsets_length]

/-- Each initial guard has a canonical row in the generated inventory. -/
def initialRow (initial : List (Guard Formula)) (guard : Guard Formula) (present : guard ∈ initial) : Row initial :=
  ⟨normalize GuardStructuralOrder.le guard,
    normalize_idempotent GuardStructuralOrder.le GuardStructuralOrder.le_trans
      GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm _, by
      intro atom member
      rw [atoms_normalize, canonical_mem] at member
      exact List.mem_flatMap.mpr ⟨guard, present, member⟩⟩

/-- A right operand need not already have canonical outer conjunction syntax. -/
theorem merge_normalize_right (first second : Guard Formula) :
    merge GuardStructuralOrder.le first (normalize GuardStructuralOrder.le second) =
      merge GuardStructuralOrder.le first second := by
  apply normalize_eq GuardStructuralOrder.le GuardStructuralOrder.le_trans
    GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm
  intro atom
  simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    atoms_normalize, canonical_mem]

/-- The actual row conjunction retains the independent source guard interpretation. -/
theorem join_exact (initial : List (Guard Formula)) (first second : Row initial)
    (solver : SourceGuards.Entailment Formula) (term : Language.Term (SourceObservations.Label Formula)) :
    SourceConstraintConjunction.meaning SourceFormula.operations solver (join initial first second).val term ↔
      SourceConstraintConjunction.meaning SourceFormula.operations solver first.val term ∧
      SourceConstraintConjunction.meaning SourceFormula.operations solver second.val term :=
  SourceConstraintConjunction.merge_exact GuardStructuralOrder.le SourceFormula.operations solver _ _ term

/-- Source Cartesian edge generation and the finite row product have exactly the same guards. -/
theorem source_product_members (initial : List (Guard Formula)) (first second : List (Row initial)) (guard : Guard Formula) :
    guard ∈ first.flatMap (fun left => second.map (fun right => merge GuardStructuralOrder.le left.val right.val)) ↔
      ∃ row, product (algebra initial) (fun row => row ∈ first) (fun row => row ∈ second) row ∧ row.val = guard := by
  constructor
  · intro present
    obtain ⟨left, firstPresent, middle⟩ := List.mem_flatMap.mp present
    obtain ⟨right, secondPresent, same⟩ := List.mem_map.mp middle
    exact ⟨join initial left right, ⟨left, right, firstPresent, secondPresent, rfl⟩, same⟩
  · rintro ⟨row, ⟨left, right, firstPresent, secondPresent, same⟩, guardEq⟩
    exact List.mem_flatMap.mpr ⟨left, firstPresent, List.mem_map.mpr ⟨right, secondPresent,
      (congrArg Subtype.val same).trans guardEq⟩⟩

/-- Arbitrary repeated source leaf-row narrowing reaches a structural fixed point.
Whole-node absorption and decreasing row counts are not premises. -/
theorem run_terminates (initial : List (Guard Formula))
    (choose : Rows (Row initial) → Rows (Row initial)) (rows : Rows (Row initial)) :
    ∃ fuel result, FiniteRowIntersection.run (algebra initial) choose fuel rows = some result ∧
      intersect (algebra initial) result (choose result) = result :=
  FiniteRowIntersection.run_terminates (algebra initial) (inventory initial) (inventory_complete initial) choose rows

end MicroCFTA.SourceLeafRowProgress
