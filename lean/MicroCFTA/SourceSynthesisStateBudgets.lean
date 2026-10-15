import MicroCFTA.RecursiveSize
import Init.Data.List.Sort.Lemmas

/-!
# Size budgets of the source synthesis-state search

The source enumerates positive child-size compositions, assigns required
arguments to children, and rejects overloaded children. This port retains
the source loop order. Natural sizes describe the nonnegative source domain.
Argument indexes remain signed. Machine conversion and host refinement
contracts are separate. The whole search and its automaton are not modeled
by this local budget theorem.
-/
namespace MicroCFTA.SourceSynthesisStateBudgets

/-- Enumerate the source's ascending positive compositions. -/
def compositions (total : Nat) : Nat → List (List Nat)
  | 0 => if total = 0 then [[]] else []
  | parts + 1 => (List.range (total - parts)).flatMap fun offset =>
      (compositions (total - (offset + 1)) parts).map ((offset + 1) :: ·)

/-- Positive sizes need at least one unit per child. -/
theorem positive_length_le_sum (sizes : List Nat) (positive : ∀ size ∈ sizes, 0 < size) :
    sizes.length ≤ sizes.sum := by
  induction sizes with
  | nil => simp
  | cons first rest ih =>
      have own := positive first List.mem_cons_self
      have tail := ih (fun size member => positive size (List.mem_cons_of_mem _ member))
      simp only [List.length_cons, List.sum_cons]
      omega

/-- The actual composition loops contain exactly the positive lists with the requested sum and length. -/
theorem compositions_exact (parts total : Nat) (sizes : List Nat) :
    sizes ∈ compositions total parts ↔
      sizes.length = parts ∧ sizes.sum = total ∧ ∀ size ∈ sizes, 0 < size := by
  induction parts generalizing total sizes with
  | zero =>
      by_cases empty : total = 0
      · subst total
        cases sizes <;> simp [compositions]
      · simp only [compositions, empty, ↓reduceIte, List.not_mem_nil, false_iff]
        rintro ⟨length, sum, _⟩
        have : sizes = [] := by simpa using length
        subst sizes
        exact empty sum.symm
  | succ parts ih =>
      constructor
      · intro member
        obtain ⟨offset, bound, rest, remaining, same⟩ :=
          (by simpa [compositions, List.mem_flatMap, List.mem_map] using member :
            ∃ offset, offset < total - parts ∧ ∃ rest,
              rest ∈ compositions (total - (offset + 1)) parts ∧ (offset + 1) :: rest = sizes)
        subst sizes
        obtain ⟨length, sum, positive⟩ := (ih _ rest).mp remaining
        refine ⟨by simp [length], ?_, ?_⟩
        · simp only [List.sum_cons, sum]
          omega
        · intro size included
          rcases List.mem_cons.mp included with rfl | included
          · omega
          · exact positive size included
      · rintro ⟨length, sum, positive⟩
        cases sizes with
        | nil => simp at length
        | cons first rest =>
            have own := positive first List.mem_cons_self
            have tail := fun size member => positive size (List.mem_cons_of_mem first member)
            have tailBound := positive_length_le_sum rest tail
            have tailLength : rest.length = parts := by simpa using length
            have tailSum : rest.sum = total - first := by simp only [List.sum_cons] at sum; omega
            have firstEq : first - 1 + 1 = first := by omega
            apply List.mem_flatMap.mpr
            refine ⟨first - 1, List.mem_range.mpr ?_, ?_⟩
            · simp only [List.sum_cons] at sum
              omega
            · exact List.mem_map.mpr ⟨rest, (ih _ rest).mpr
                ⟨tailLength, by simpa only [firstEq] using tailSum, tail⟩,
                by simp only [firstEq]⟩

/-- Insert one required argument into the chosen child and retain sorted indexes. -/
def assign (argument : Int) (chosen : Nat) (sets : List (List Int)) : List (List Int) :=
  sets.zipIdx.map fun (set, child) =>
    if child = chosen then (argument :: set).mergeSort (· ≤ ·) else set

/-- The source argument loop tries every child after each assignment of the remaining arguments. -/
def assignments : List Int → Nat → List (List (List Int))
  | [], parts => [List.replicate parts []]
  | argument :: rest, parts => (assignments rest parts).flatMap fun sets =>
      (List.range parts).map fun chosen => assign argument chosen sets

/-- Inserting an argument does not change the number of children. -/
theorem assign_length (argument : Int) (chosen : Nat) (sets : List (List Int)) :
    (assign argument chosen sets).length = sets.length := by simp [assign]

/-- Every source assignment has exactly one argument list per child. -/
theorem assignments_length (arguments : List Int) (parts : Nat)
    (sets : List (List Int)) (member : sets ∈ assignments arguments parts) :
    sets.length = parts := by
  induction arguments generalizing sets with
  | nil =>
      have same : sets = List.replicate parts [] := by simpa [assignments] using member
      simp [same]
  | cons argument rest ih =>
      obtain ⟨original, earlier, chosen, _, rfl⟩ :=
        (by simpa [assignments, List.mem_flatMap, List.mem_map] using member :
          ∃ original, original ∈ assignments rest parts ∧ ∃ chosen,
            chosen < parts ∧ assign argument chosen original = sets)
      exact (assign_length _ _ _).trans (ih original earlier)

/-- The actual unfiltered source loop combines sizes and argument assignments in their original order. -/
def every (total : Nat) (arguments : List Int) (parts : Nat) : List (List (Nat × List Int)) :=
  (compositions total parts).flatMap fun sizes =>
    (assignments arguments parts).map fun sets => sizes.zip sets

/-- The source retains exactly the splits whose argument counts fit each child's size. -/
def budgetSplits (total : Nat) (arguments : List Int) (parts : Nat) :
    List (List (Nat × List Int)) × Nat :=
  let all := every total arguments parts
  let kept := all.filter fun split => split.all fun (size, required) => required.length ≤ size
  (kept, all.length - kept.length)

/-- Kept splits have their original source witnesses and satisfy every argument bound. -/
theorem budgetSplits_exact (total : Nat) (arguments : List Int) (parts : Nat)
    (split : List (Nat × List Int)) :
    split ∈ (budgetSplits total arguments parts).1 ↔
      (∃ sizes ∈ compositions total parts, ∃ sets ∈ assignments arguments parts,
        sizes.zip sets = split) ∧ ∀ child ∈ split, child.2.length ≤ child.1 := by
  simp [budgetSplits, every, List.mem_flatMap, List.mem_map, List.all_eq_true]

/-- The discarded count and retained count account for every original split occurrence. -/
theorem budgetSplits_accounting (total : Nat) (arguments : List Int) (parts : Nat) :
    (budgetSplits total arguments parts).1.length + (budgetSplits total arguments parts).2 =
      (every total arguments parts).length := by
  have bound := List.length_filter_le
    (fun split : List (Nat × List Int) => split.all fun child => child.2.length ≤ child.1)
    (every total arguments parts)
  simp only [budgetSplits]
  omega

/-- Every retained split has the requested number of children. -/
theorem budgetSplits_length {total arguments parts split}
    (member : split ∈ (budgetSplits total arguments parts).1) : split.length = parts := by
  obtain ⟨⟨sizes, sizeMember, sets, setMember, rfl⟩, _⟩ := (budgetSplits_exact _ _ _ _).mp member
  simp only [List.length_zip, (compositions_exact _ _ _).mp sizeMember |>.1,
    assignments_length _ _ _ setMember, Nat.min_self]

/-- Child sizes retain the whole size budget after the parent consumes its root. -/
theorem budgetSplits_size {total arguments parts split}
    (member : split ∈ (budgetSplits total arguments parts).1) :
    (split.map Prod.fst).sum = total := by
  obtain ⟨⟨sizes, sizeMember, sets, setMember, rfl⟩, _⟩ := (budgetSplits_exact _ _ _ _).mp member
  have sizeFacts := (compositions_exact _ _ _).mp sizeMember
  have setLength := assignments_length _ _ _ setMember
  rw [List.map_fst_zip (by omega)]
  exact sizeFacts.2.1

/-- Each source child consumes a positive size strictly below its parent's root-inclusive size. -/
theorem budgetSplits_child {total arguments parts split} (member : split ∈ (budgetSplits total arguments parts).1)
    (child : Nat × List Int) (included : child ∈ split) :
    0 < child.1 ∧ child.1 < total + 1 ∧ child.2.length ≤ child.1 := by
  obtain ⟨⟨sizes, sizeMember, sets, _, same⟩, bounded⟩ := (budgetSplits_exact _ _ _ _).mp member
  have sizeIncluded := (List.of_mem_zip (same ▸ included)).1
  have exactSize := (compositions_exact _ _ _).mp sizeMember
  have bound : child.1 ≤ sizes.sum := by
    have localBound : ∀ (items : List Nat) (size : Nat), size ∈ items → size ≤ items.sum := by
      intro items size member
      induction items with
      | nil => simp at member
      | cons first rest ih =>
          simp only [List.sum_cons]
          rcases List.mem_cons.mp member with rfl | member
          · omega
          · have := ih member; omega
    exact localBound _ _ sizeIncluded
  exact ⟨exactSize.2.2 _ sizeIncluded, by omega, bounded child included⟩

end MicroCFTA.SourceSynthesisStateBudgets
