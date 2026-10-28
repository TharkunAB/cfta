import MicroCFTA.SourcePruningEnumerationModelPathDomain
import MicroCFTA.SourceEqualityConstraintPathInventory
import MicroCFTA.SymbolicSelection

/-!
# Finite trie shapes of a modeled stored recursion key

The original term supplies a finite relative path domain.
Bounded lists enumerate each trie shape and the whole trie-list shape.
The native handle and attached historical keys are outside this statement.
-/
namespace MicroCFTA.SourcePruningEnumerationModelKeyShapes
open Language EnumerationState EnumerationCorrectness EnumerationValidity
open SourcePruningEnumerationOrigins SourcePruningEnumerationModelPathDomain
open SourceEqualityConstraintPathInventory (lists mem_lists)
variable {Symbol Guard : Type}

/-- Enumerate every bounded trie path list over the original relative domain. -/
def trieShapes (whole : Term Symbol) : List (List (List Nat)) :=
  lists (relativePaths whole) (relativePaths whole).length

/-- Enumerate bounded lists of the finite trie shapes. -/
def keyShapes (whole : Term Symbol) : List (List (List (List Nat))) :=
  lists (trieShapes whole) (trieShapes whole).length

/-- The actual stored recursion key has a trie list in the original finite carrier. -/
theorem stored_recursion_key_mem
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (state : State Symbol Guard) (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment state)
    (origins : AssignmentOrigins whole state.counter assignment)
    (canonical : Canonical state)
    {uv handle : Nat} {scs : List Suspended}
    (inside : uv < state.counter)
    (stored : state.values[uv]? = some (.unenumerated (some handle) scs)) :
    (EnumerationState.recursionKey handle scs).tries ∈ keyShapes whole := by
  have paths := stored_recursion_key_paths language meaning state whole assignment
    satisfied origins canonical inside stored
  have subset : ∀ trie ∈ (EnumerationState.recursionKey handle scs).tries,
      trie ∈ trieShapes whole := by
    intro trie member
    exact (mem_lists _ _ _).mpr ⟨(paths trie member).2, (paths trie member).1⟩
  have unique : (EnumerationState.recursionKey handle scs).tries.Nodup :=
    (List.mergeSort_perm _ _).symm.nodup (SymbolicDriver.eraseDups_nodup _)
  exact (mem_lists _ _ _).mpr ⟨unique.length_le_of_subset subset, subset⟩

end MicroCFTA.SourcePruningEnumerationModelKeyShapes
