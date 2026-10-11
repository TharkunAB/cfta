import MicroCFTA.UnionFind

/-!
# The parent-array operations used by equality completion

The source array stores each root as its own parent. It compresses paths and
links the left root to the right root without a size comparison. Root sizes
in the existing forest proof are ghost data and are erased here.
-/
namespace MicroCFTA.ArrayUnionFind
open UnionFind

/-- Functional reads of the source's mutable parent array. -/
abbrev Parents := Nat → Nat

/-- Erase root-size proof data to the source's self-parent representation. -/
def erase (forest : Forest) : Parents := fun index =>
  match read forest index with
  | .root _ => index
  | .parent above => above

/-- One source parent-array write. -/
def write (parents : Parents) (index value : Nat) : Parents :=
  fun other => if other = index then value else parents other

/-- A parent write has the same effect before and after erasure. -/
theorem erase_parent (forest : Forest) (index value : Nat) :
    erase (put forest index (.parent value)) = write (erase forest) index value := by
  funext other
  by_cases same : other = index <;> simp [erase, write, UnionFind.read, put, same]

/-- Storing a root changes no self-parent entry when it is already a root. -/
theorem erase_root (forest : Forest) (index oldSize newSize : Nat)
    (root : read forest index = .root oldSize) : erase (put forest index (.root newSize)) = erase forest := by
  funext other
  by_cases same : other = index
  · subst other; simp [erase, root]
  · simp [erase, read_put_other _ _ _ _ same]

/-- A finite root path cannot contain a self-parent pointer. -/
theorem no_self_parent (path : Reaches forest index root size) : read forest index ≠ .parent index := by
  induction path with
  | root lookup => simp [lookup]
  | @parent index above root size lookup tail ih =>
      intro same
      have equal : above = index := Entry.parent.inj (lookup.symm.trans same)
      subst above
      exact ih same

/-- The source path-compressing array lookup with an explicit execution bound. -/
def find : Nat → Parents → Nat → Option (Nat × Parents)
  | 0, _, _ => none
  | fuel + 1, parents, index =>
      let above := parents index
      if above = index then some (index, parents)
      else do
        let (root, after) ← find fuel parents above
        pure (root, write after index root)

/-- Every successful proved forest lookup has the identical source array execution. -/
theorem find_refines (fuel : Nat) (forest : Forest) (valid : Total forest) (index : Nat) (result : Result)
    (success : findRoot fuel forest index = some result) :
    find fuel (erase forest) index = some (result.representative, erase result.forest) := by
  induction fuel generalizing forest index result with
  | zero => simp [findRoot] at success
  | succ fuel ih =>
      cases lookup : forest index with
      | none =>
          have same : result = ⟨index, 1, put forest index (.root 1)⟩ := by
            simpa [findRoot, lookup] using success.symm
          subst result
          have root : read forest index = .root 1 := by simp [UnionFind.read, lookup]
          rw [erase_root forest index 1 1 root]
          simp [find, erase, root]
      | some entry =>
          cases entry with
          | root size =>
              have same : result = ⟨index, size, forest⟩ := by simpa [findRoot, lookup] using success.symm
              subst result
              simp [find, erase, UnionFind.read, lookup]
          | parent above =>
              have parent : read forest index = .parent above := by simp [UnionFind.read, lookup]
              have different : above ≠ index := by
                intro same
                obtain ⟨root, size, path⟩ := valid index
                exact no_self_parent path (same ▸ parent)
              cases recursive : findRoot fuel forest above with
              | none => simp [findRoot, lookup, recursive] at success
              | some found =>
                  have same : result = {found with forest := put found.forest index (.parent found.representative)} :=
                    by simpa [findRoot, lookup, recursive] using success.symm
                  subst result
                  have executed := ih forest valid above found recursive
                  simp only [find, erase, parent, ite_eq_right different]
                  change (do
                    let (root, after) ← find fuel (erase forest) above
                    pure (root, write after index root)) = _
                  rw [executed]
                  simp [erase_parent]

/-- Source array lookup terminates for each index of a total forest. -/
theorem find_terminates (forest : Forest) (valid : Total forest) (index : Nat) :
    ∃ fuel root after, find fuel (erase forest) index = some (root, after) := by
  obtain ⟨root, size, path⟩ := valid index
  obtain ⟨fuel, result, success⟩ := findRoot_terminates path
  exact ⟨fuel, result.representative, erase result.forest, find_refines fuel forest valid index result success⟩

/-- The source always links the first root to the second root. -/
def unionLeft (leftFuel rightFuel : Nat) (forest : Forest) (left right : Nat) : Option Forest := do
  let first ← findRoot leftFuel forest left
  let second ← findRoot rightFuel first.forest right
  if first.representative = second.representative then some second.forest
  else some (link second.forest first.representative second.representative first.size second.size)

/-- Unweighted source linking merges exactly the requested two classes. -/
theorem unionLeft_correct (valid : Total forest)
    (result : unionLeft leftFuel rightFuel forest left right = some output) :
    Total output ∧ ∀ x y,
      SameClass output x y ↔
        SameClass forest x y ∨
        (SameClass forest x left ∧ SameClass forest y right) ∨
        (SameClass forest x right ∧ SameClass forest y left) := by
  cases firstResult : findRoot leftFuel forest left with
  | none => simp [unionLeft, firstResult] at result
  | some first =>
    cases secondResult : findRoot rightFuel first.forest right with
    | none => simp [unionLeft, firstResult, secondResult] at result
    | some second =>
      have firstValid := findRoot_total valid firstResult
      have secondValid := findRoot_total firstValid secondResult
      have leftPath := (findRoot_correct _ _ _ _ secondResult).2
        ((findRoot_correct _ _ _ _ firstResult).2 (findRoot_correct _ _ _ _ firstResult).1)
      have rightPath := (findRoot_correct _ _ _ _ secondResult).2
        (findRoot_correct _ _ _ _ secondResult).1
      have leftRoot := reaches_terminal leftPath
      have rightRoot := reaches_terminal rightPath
      have unchanged (x y : Nat) : SameClass second.forest x y ↔ SameClass forest x y :=
        (findRoot_classes firstValid secondResult x y).trans (findRoot_classes valid firstResult x y)
      by_cases same : first.representative = second.representative
      · simp [unionLeft, firstResult, secondResult, same] at result
        subst output
        refine ⟨secondValid, ?_⟩
        have sameBefore : SameClass forest left right :=
          (unchanged left right).mp ((sameClass_iff_roots leftPath rightPath).mpr same)
        intro x y
        exact (unchanged x y).trans (redundant_merge sameBefore x y).symm
      · simp [unionLeft, firstResult, secondResult, same] at result
        subst output
        refine ⟨link_total secondValid leftRoot rightRoot same, ?_⟩
        intro x y
        rw [link_classes secondValid leftRoot rightRoot same]
        simp only [root_membership secondValid leftPath, root_membership secondValid rightPath, unchanged]

/-- Ghost size updates erase to the source's single left-root parent write. -/
theorem erase_link (forest : Forest) (left right leftSize rightSize : Nat)
    (different : left ≠ right) (root : read forest right = .root rightSize) :
    erase (link forest left right leftSize rightSize) = write (erase forest) left right := by
  unfold link
  rw [erase_root (put forest left (.parent right)) right rightSize (leftSize + rightSize)
    (by rw [read_put_other _ _ _ _ different.symm]; exact root)]
  exact erase_parent forest left right

/-- The exact source parent-array union worker. -/
def union (leftFuel rightFuel : Nat) (parents : Parents) (left right : Nat) : Option Parents := do
  let (leftRoot, first) ← find leftFuel parents left
  let (rightRoot, second) ← find rightFuel first right
  if leftRoot = rightRoot then some second else some (write second leftRoot rightRoot)

/-- Both compressing finds and the unweighted link refine the actual array worker. -/
theorem union_refines (forest : Forest) (valid : Total forest) (leftFuel rightFuel left right : Nat) (output : Forest)
    (success : unionLeft leftFuel rightFuel forest left right = some output) :
    union leftFuel rightFuel (erase forest) left right = some (erase output) := by
  cases firstResult : findRoot leftFuel forest left with
  | none => simp [unionLeft, firstResult] at success
  | some first =>
      cases secondResult : findRoot rightFuel first.forest right with
      | none => simp [unionLeft, firstResult, secondResult] at success
      | some second =>
          have firstValid := findRoot_total valid firstResult
          have firstRun := find_refines leftFuel forest valid left first firstResult
          have secondRun := find_refines rightFuel first.forest firstValid right second secondResult
          have rightRoot := reaches_terminal ((findRoot_correct _ _ _ _ secondResult).2
            (findRoot_correct _ _ _ _ secondResult).1)
          by_cases same : first.representative = second.representative
          · have equal : output = second.forest := by
              simpa [unionLeft, firstResult, secondResult, same] using success.symm
            subst output
            simp [union, firstRun, secondRun, same]
          · have equal : output = link second.forest first.representative second.representative first.size second.size := by
              simpa [unionLeft, firstResult, secondResult, same] using success.symm
            subst output
            simp [union, firstRun, secondRun, same, erase_link _ _ _ _ _ same rightRoot]

/-- Unweighted linking always has sufficient finite execution bounds. -/
theorem unionLeft_terminates (forest : Forest) (valid : Total forest) (left right : Nat) :
    ∃ leftFuel rightFuel output, unionLeft leftFuel rightFuel forest left right = some output := by
  obtain ⟨root, size, path⟩ := valid left
  obtain ⟨leftFuel, first, firstResult⟩ := findRoot_terminates path
  obtain ⟨root', size', path'⟩ := findRoot_total valid firstResult right
  obtain ⟨rightFuel, second, secondResult⟩ := findRoot_terminates path'
  refine ⟨leftFuel, rightFuel, ?_⟩
  simp [unionLeft, firstResult, secondResult]
  split <;> exact ⟨_, rfl⟩

/-- The array worker terminates and changes exactly the requested equivalence classes. -/
theorem union_terminates_exact (forest : Forest) (valid : Total forest) (left right : Nat) :
    ∃ leftFuel rightFuel output,
      union leftFuel rightFuel (erase forest) left right = some (erase output) ∧ Total output ∧
      ∀ x y, SameClass output x y ↔ SameClass forest x y ∨
        (SameClass forest x left ∧ SameClass forest y right) ∨
        (SameClass forest x right ∧ SameClass forest y left) := by
  obtain ⟨leftFuel, rightFuel, output, success⟩ := unionLeft_terminates forest valid left right
  exact ⟨leftFuel, rightFuel, output, union_refines forest valid leftFuel rightFuel left right output success,
    unionLeft_correct valid success⟩

/-- The source array initializer is the erased singleton forest. -/
theorem initial_array (variables : List Nat) : erase (withInitialValues variables) = id := by
  funext index
  simp [erase, read_initial]

end MicroCFTA.ArrayUnionFind
