import MicroCFTA.SourceEqualityEditMeaning

/-!
# Independent path readback of retained edit leaves

The finite trie exposes each retained callback with its complete signed path.
Its term condition checks the callback only when that complete path exists.
Prefix shadowing remains in the compiler's retained leaf list.
-/
namespace MicroCFTA.SourceEqualityEditLeafPaths
open Language SourceEqualityEdits SourceEqualityEditMeaning

/-- List each retained callback with its complete signed path from the current root. -/
def leaves : Edits Action → List (Path × Action)
  | .editAt action => [([], action)]
  | .editBelow children => children.flatMap fun entry =>
      (leaves entry.2).map (fun leaf => (entry.1 :: leaf.1, leaf.2))
termination_by edits => sizeOf edits
decreasing_by
  have smaller := List.sizeOf_lt_of_mem ‹entry ∈ children›
  cases entry
  simp only [Prod.mk.sizeOf_spec, Edits.editBelow.sizeOf_spec] at *
  omega

/-- A stored child leaf retains its first signed path step. -/
theorem below_member (entries : List (Int × Edits Action)) (index : Int) (child : Edits Action)
    (member : (index, child) ∈ entries) (path : Path) (action : Action)
    (retained : (path, action) ∈ leaves child) :
    (index :: path, action) ∈ leaves (.editBelow entries) := by
  rw [leaves]
  exact List.mem_flatMap.mpr ⟨(index, child), member, List.mem_map.mpr ⟨(path, action), retained, rfl⟩⟩

/-- A trie condition is exactly its retained callback conditions at existing complete paths. -/
theorem matches_exact (condition : Action → Term Symbol → Prop) (edits : Edits Action) (term : Term Symbol) :
    Matches condition edits term ↔ ∀ path action, (path, action) ∈ leaves edits →
      ∀ part, SymbolicSignedPaths.lookup term path = some part → condition action part := by
  cases shape : edits with
  | editAt action =>
      simp [Matches, leaves, SymbolicSignedPaths.lookup]
  | editBelow entries =>
      cases term with
      | node symbol terms =>
          rw [Matches]
          constructor
          · intro allChildren path action member part found
            rw [leaves] at member
            obtain ⟨⟨index, child⟩, childMember, leafMember⟩ := List.mem_flatMap.mp member
            obtain ⟨⟨suffix, actual⟩, retained, same⟩ := List.mem_map.mp leafMember
            have pair := Prod.mk.inj same
            cases pair.1
            cases pair.2
            rw [SourceEqualityNeededMeaning.lookup_cons] at found
            obtain ⟨subtree, selected, reached⟩ := Option.bind_eq_some_iff.mp found
            exact (matches_exact condition child subtree).mp (allChildren index child childMember subtree selected)
              suffix actual retained part reached
          · intro allPaths index child member subtree selected
            apply (matches_exact condition child subtree).mpr
            intro path action retained part reached
            exact allPaths (index :: path) action (below_member entries index child member path action retained) part
              (by rw [SourceEqualityNeededMeaning.lookup_cons, selected, Option.bind_some, reached])
termination_by sizeOf edits
decreasing_by
  all_goals
    have smaller := List.sizeOf_lt_of_mem ‹(_, child) ∈ entries›
    simp only [Prod.mk.sizeOf_spec, Edits.editBelow.sizeOf_spec] at *
    omega

end MicroCFTA.SourceEqualityEditLeafPaths
