import MicroCFTA.SourceEqualityNeeded

/-!
# Nonnegative keys throughout compiled required-path tries

The source trie keeps signed keys. Independent path-preservation theorems
use the normalized nonnegative path domain. This property follows the actual
right fold and alter operation; it does not replace source keys by naturals.
-/
namespace MicroCFTA.SourceEqualityNeededNonnegative
open SourceEqualityNeeded SourceEqualityNeededMap

/-- Every stored child key and every descendant key is nonnegative. -/
def Nonnegative : Needed → Prop
  | .node children => ∀ index child, (index, child) ∈ children → 0 ≤ index ∧ Nonnegative child
termination_by needed => sizeOf needed
decreasing_by
  have smaller := List.sizeOf_lt_of_mem ‹(index, child) ∈ children›
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- Empty requirements contain no negative key. -/
theorem empty_nonnegative : Nonnegative empty := by simp [Nonnegative, empty]

/-- Inserting a normalized source path preserves nonnegative keys at every depth. -/
theorem insert_nonnegative (path : Path) (needed : Needed) (valid : Valid needed)
    (nonnegative : Nonnegative needed) (indices : ∀ index ∈ path, 0 ≤ index) :
    Nonnegative (insert path needed) := by
  induction path generalizing needed with
  | nil => exact nonnegative
  | cons index rest ih =>
      cases needed with
      | node children =>
          rw [Valid] at valid
          rw [Nonnegative] at nonnegative
          have previousValid : Valid ((lookup index children).getD empty) := by
            cases found : lookup index children with
            | none => exact empty_valid
            | some child => exact valid.2 index child (lookup_mem _ _ _ found)
          have previousNonnegative : Nonnegative ((lookup index children).getD empty) := by
            cases found : lookup index children with
            | none => exact empty_nonnegative
            | some child => exact (nonnegative index child (lookup_mem _ _ _ found)).2
          have inserted := ih _ previousValid previousNonnegative
            (fun key member => indices key (List.mem_cons_of_mem _ member))
          have childrenNonnegative := alter_all index (fun previous => insert rest (previous.getD empty)) children Nonnegative
            (fun key child member => (nonnegative key child member).2) inserted valid.1
          rw [SourceEqualityNeeded.insert, Nonnegative]
          intro key child member
          refine ⟨?_, childrenNonnegative key child member⟩
          rcases alter_origin index (fun previous => insert rest (previous.getD empty)) children (key, child) member with same | original
          · change key = index at same
            simpa only [same] using indices index List.mem_cons_self
          · exact (nonnegative key child original).1

/-- The actual Needed compiler retains the normalization premise for every child requirement. -/
theorem build_nonnegative (paths : List Path)
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index) : Nonnegative (build paths) := by
  induction paths with
  | nil => exact empty_nonnegative
  | cons path rest ih =>
      exact insert_nonnegative path (build rest) (build_valid rest)
        (ih (fun original member => indices original (List.mem_cons_of_mem _ member)))
        (indices path List.mem_cons_self)

end MicroCFTA.SourceEqualityNeededNonnegative
