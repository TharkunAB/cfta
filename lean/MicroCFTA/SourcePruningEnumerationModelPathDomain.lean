import MicroCFTA.SourcePruningEnumerationOrigins
import MicroCFTA.EqualitySaturation
import MicroCFTA.EnumerationValidity

/-!
# Finite relative paths from an original assignment model

A suspended path is relative to its stored variable's assigned subtree.
The domain includes the existing paths of every subtree of the original term.
A satisfying stored bucket uses only paths from that finite domain.
-/
namespace MicroCFTA.SourcePruningEnumerationModelPathDomain
open Language EnumerationState EnumerationCorrectness EnumerationValidity
open SourcePruningEnumerationOrigins
variable {Symbol Guard : Type}

/-- Enumerate the relative paths that exist in any subtree of the original term. -/
def relativePaths (whole : Term Symbol) : List (List Nat) :=
  (EqualitySaturation.termPaths whole).flatMap (fun base =>
    match whole.atPath base with
    | none => []
    | some part => EqualitySaturation.termPaths part)

/-- Every existing path in an original subtree lies in the finite relative domain. -/
theorem origin_path_mem {whole term part : Term Symbol} {path : List Nat}
    (origin : Origin whole term) (located : term.atPath path = some part) :
    path ∈ relativePaths whole := by
  obtain ⟨base, original⟩ := origin
  apply List.mem_flatMap.mpr
  refine ⟨base, (EqualitySaturation.termPaths_correct whole base).mpr ⟨term, original⟩, ?_⟩
  simpa only [original] using (EqualitySaturation.termPaths_correct term path).mpr ⟨part, located⟩

/-- A stored satisfying bucket has finite relative paths and an original-term height bound. -/
theorem stored_suspended_paths
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (state : State Symbol Guard) (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment state)
    (origins : AssignmentOrigins whole state.counter assignment)
    {uv : Nat} {node : Option Nat} {scs : List Suspended}
    (inside : uv < state.counter)
    (stored : state.values[uv]? = some (.unenumerated node scs)) :
    ∀ sc ∈ scs, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
      path ∈ relativePaths whole ∧ (assignment sc.var).height + path.length ≤ whole.height := by
  have model := satisfied.1.2 uv
  simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
    List.forall_mem_map] at model
  intro sc member path represented
  have located := model.2 sc member path represented
  exact ⟨origin_path_mem (origins uv inside) located,
    Nat.le_trans (atPath_height_bound _ _ _ located) (origin_height _ _ (origins uv inside))⟩

/-- A valid stored trie has no more represented paths than the original finite domain. -/
theorem stored_trie_length
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (state : State Symbol Guard) (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment state)
    (origins : AssignmentOrigins whole state.counter assignment)
    (canonical : Canonical state)
    {uv : Nat} {node : Option Nat} {scs : List Suspended}
    (inside : uv < state.counter)
    (stored : state.values[uv]? = some (.unenumerated node scs)) :
    ∀ sc ∈ scs, (EqualityTrie.fromPathTrie sc.trie).length ≤ (relativePaths whole).length := by
  intro sc member
  have valid : EqualityTrie.Valid sc.trie :=
    (canonical _ (List.mem_of_getElem? stored)) sc member
  have unique := EqualityTrie.supported_nodup _ (EqualityTrie.fromPathTrie_supported _ valid)
  exact unique.length_le_of_subset (fun path represented =>
    (stored_suspended_paths language meaning state whole assignment satisfied origins inside stored
      sc member path represented).1)

end MicroCFTA.SourcePruningEnumerationModelPathDomain

namespace MicroCFTA.SourcePruningEnumerationModelPathDomain
open Language EnumerationState EnumerationCorrectness EnumerationValidity
open SourcePruningEnumerationOrigins
variable {Symbol Guard : Type}

/-- The actual stored recursion key retains the finite original relative path bounds. -/
theorem stored_recursion_key_paths
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (state : State Symbol Guard) (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment state)
    (origins : AssignmentOrigins whole state.counter assignment)
    (canonical : Canonical state)
    {uv handle : Nat} {scs : List Suspended}
    (inside : uv < state.counter)
    (stored : state.values[uv]? = some (.unenumerated (some handle) scs)) :
    ∀ trie ∈ (EnumerationState.recursionKey handle scs).tries,
      (∀ path ∈ trie, path ∈ relativePaths whole) ∧
      trie.length ≤ (relativePaths whole).length := by
  intro trie member
  have source : trie ∈ scs.map (fun sc => EqualityTrie.fromPathTrie sc.trie) := by
    simpa only [EnumerationState.recursionKey, List.mem_mergeSort, List.mem_eraseDups]
      using member
  obtain ⟨sc, present, rfl⟩ := List.mem_map.mp source
  constructor
  · intro path represented
    exact (stored_suspended_paths language meaning state whole assignment satisfied origins inside stored
      sc present path represented).1
  · exact stored_trie_length language meaning state whole assignment satisfied origins canonical inside stored
      sc present

end MicroCFTA.SourcePruningEnumerationModelPathDomain
