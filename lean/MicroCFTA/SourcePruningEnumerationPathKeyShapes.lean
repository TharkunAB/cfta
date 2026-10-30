import MicroCFTA.SourcePruningEnumerationPathTransport
import MicroCFTA.EnumerationValidity
import MicroCFTA.SourceEqualityConstraintPathInventory
import MicroCFTA.SymbolicSelection

/-!
# Finite recursion-key shapes from a supplied original path domain

Every stored path belongs to the same finite domain.
Canonical tries have no duplicate represented paths.
The actual recursion key removes duplicate trie shapes.
The native handle remains outside this carrier.
-/
namespace MicroCFTA.SourcePruningEnumerationPathKeyShapes
open EnumerationState EnumerationValidity
open SourcePruningEnumerationPathTransport
open SourceEqualityConstraintPathInventory (lists mem_lists)
variable {Symbol Guard : Type}

/-- Enumerate every bounded trie path list over the finite domain. -/
def trieShapes (domain : List EqualityTrie.Path) : List (List EqualityTrie.Path) :=
  lists domain domain.length

/-- Enumerate every bounded list of finite trie shapes. -/
def keyShapes (domain : List EqualityTrie.Path) : List (List (List EqualityTrie.Path)) :=
  lists (trieShapes domain) (trieShapes domain).length

/-- Every actual stored key trie stays within the supplied finite path domain. -/
theorem stored_recursion_key_paths
    (domain : List EqualityTrie.Path) (state : State Symbol Guard)
    (paths : StatePaths (fun path => path ∈ domain) state)
    (canonical : Canonical state)
    {uv handle : Nat} {scs : List Suspended}
    (stored : state.values[uv]? = some (.unenumerated (some handle) scs)) :
    ∀ trie ∈ (recursionKey handle scs).tries,
      (∀ path ∈ trie, path ∈ domain) ∧ trie.length ≤ domain.length := by
  intro trie member
  have source : trie ∈ scs.map (fun sc => EqualityTrie.fromPathTrie sc.trie) := by
    simpa only [recursionKey, List.mem_mergeSort, List.mem_eraseDups] using member
  obtain ⟨sc, present, rfl⟩ := List.mem_map.mp source
  have bucket : BucketPaths (fun path => path ∈ domain) scs :=
    paths _ (List.mem_of_getElem? stored)
  have valid : EqualityTrie.Valid sc.trie :=
    (canonical _ (List.mem_of_getElem? stored)) sc present
  have unique := EqualityTrie.supported_nodup _ (EqualityTrie.fromPathTrie_supported _ valid)
  exact ⟨bucket sc present, unique.length_le_of_subset (bucket sc present)⟩

/-- Every actual stored key has its trie-list shape in the finite carrier. -/
theorem stored_recursion_key_mem
    (domain : List EqualityTrie.Path) (state : State Symbol Guard)
    (paths : StatePaths (fun path => path ∈ domain) state)
    (canonical : Canonical state)
    {uv handle : Nat} {scs : List Suspended}
    (stored : state.values[uv]? = some (.unenumerated (some handle) scs)) :
    (recursionKey handle scs).tries ∈ keyShapes domain := by
  have represented := stored_recursion_key_paths domain state paths canonical stored
  have subset : ∀ trie ∈ (recursionKey handle scs).tries, trie ∈ trieShapes domain := by
    intro trie member
    exact (mem_lists _ _ _).mpr ⟨(represented trie member).2, (represented trie member).1⟩
  have unique : (recursionKey handle scs).tries.Nodup :=
    (List.mergeSort_perm _ _).symm.nodup (SymbolicDriver.eraseDups_nodup _)
  exact (mem_lists _ _ _).mpr ⟨unique.length_le_of_subset subset, subset⟩

end MicroCFTA.SourcePruningEnumerationPathKeyShapes
