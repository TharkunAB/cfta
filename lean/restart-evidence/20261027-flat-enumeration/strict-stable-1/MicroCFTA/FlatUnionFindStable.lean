import MicroCFTA.FlatUnionFindRefinement
import MicroCFTA.EnumerationExecution

/-!
# Stable bounds for the earlier union-find calls

Enumeration uses one bound for both union lookups. The existing fuel extension
theorem supplies that common bound without changing the returned forest.
-/

namespace MicroCFTA.FlatUnionFind

/-- Every later sufficient lookup bound returns the same earlier result. -/
theorem find_stable (related : Represents flat earlier) (uv : Nat) :
    ∃ fuel found,
      (∀ extra, UnionFind.findRoot (fuel + extra) earlier uv = some found) ∧
      found.representative = root flat uv ∧
      found.size = (entryOf flat (root flat uv)).1 ∧ Represents flat found.forest := by
  obtain ⟨fuel, found, completed⟩ := UnionFind.findRoot_terminates (related uv)
  obtain ⟨sameRoot, sameSize, retained⟩ := findRoot_represents related completed
  exact ⟨fuel, found, fun extra => UnionFind.findRoot_moreFuel fuel extra earlier uv found completed,
    sameRoot, sameSize, retained⟩

/-- One common bound and every extension give the same related earlier union forest. -/
theorem union_stable (valid : Valid flat) (related : Represents flat earlier) (left right : Nat) :
    ∃ fuel output,
      (∀ extra, UnionFind.union (fuel + extra) (fuel + extra) earlier left right = some output) ∧
      Valid (union flat left right) ∧ Represents (union flat left right) output := by
  obtain ⟨afterValid, leftFuel, rightFuel, output, completed, afterRelated⟩ :=
    union_refines valid related left right
  let fuel := max leftFuel rightFuel
  have common : UnionFind.union fuel fuel earlier left right = some output := by
    have extended := EnumerationExecution.union_moreFuel leftFuel rightFuel
      (fuel - leftFuel) (fuel - rightFuel) earlier left right output completed
    simpa only [Nat.add_sub_of_le (Nat.le_max_left leftFuel rightFuel),
      Nat.add_sub_of_le (Nat.le_max_right leftFuel rightFuel)] using extended
  exact ⟨fuel, output, fun extra => EnumerationExecution.union_moreFuel fuel fuel extra extra
    earlier left right output common, afterValid, afterRelated⟩

end MicroCFTA.FlatUnionFind
