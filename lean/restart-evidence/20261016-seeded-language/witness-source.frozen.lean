import MicroCFTA.SourceEmptinessClassFold

/-!
# Common proper subtrees of satisfied source classes

An active satisfied class selects one existing subtree at every class path.
The subtree has smaller height than the parent. Natural-to-signed path
conversion and the literal first-seed rotation preserve these lookups.
These facts do not assume a projection, native result, or query language.
-/
namespace MicroCFTA.SourceCurrentConjunctionClassWitness
open Language EqualityNormalize

/-- An active source class has a literal first path. -/
theorem class_nonempty (paths : Class) (active : Nontrivial paths) : paths ≠ [] := by
  obtain ⟨first, member, _, _, _⟩ := active
  intro empty
  rw [empty] at member
  cases member

/-- Every path of a satisfied active class selects the same strictly smaller subtree. -/
theorem class_common (term : Term Symbol) (paths : Class) (active : Nontrivial paths)
    (satisfied : ClassSat term paths) :
    ∃ part, (∀ path ∈ paths, term.atPath path = some part) ∧ part.height < term.height := by
  obtain ⟨first, firstMember, other, otherMember, different⟩ := active
  have active : Nontrivial paths := ⟨first, firstMember, other, otherMember, different⟩
  obtain ⟨part, found⟩ := class_member_exists term paths active satisfied first firstMember
  refine ⟨part, ?_, ?_⟩
  · intro path member
    obtain ⟨common, firstFound, pathFound⟩ := class_pair_equal term paths active satisfied first path firstMember member
    have same : common = part := Option.some.inj (firstFound.symm.trans found)
    exact same ▸ pathFound
  · have nonroot := EqualityReduction.class_nonroot paths active term satisfied first firstMember
    have bound := atPath_height_bound term part first found
    have positive : 0 < first.length := List.length_pos_iff.mpr nonroot
    omega

/-- Actual signed source paths retain the same common proper subtree. -/
theorem class_signed_common (term : Term Symbol) (paths : Class) (active : Nontrivial paths)
    (satisfied : ClassSat term paths) :
    ∃ part, (∀ path ∈ paths.map (List.map Int.ofNat), SymbolicSignedPaths.lookup term path = some part) ∧
      part.height < term.height := by
  obtain ⟨part, selected, smaller⟩ := class_common term paths active satisfied
  refine ⟨part, ?_, smaller⟩
  intro path member
  obtain ⟨natural, present, rfl⟩ := List.mem_map.mp member
  rw [SourceEqualitySelectedRequired.lookup_natural]
  exact selected natural present

/-- The literal first-seed rotation retains exactly the original common lookups. -/
theorem rotated_common (term : Term Symbol) (paths : List (List Int)) (part : Term Symbol) :
    (∀ path ∈ SourceEmptinessClassFold.seededPaths paths, SymbolicSignedPaths.lookup term path = some part) ↔
      ∀ path ∈ paths, SymbolicSignedPaths.lookup term path = some part := by
  constructor
  · intro common path member
    exact common path ((SourceEmptinessClassFold.mem_seededPaths paths path).mpr member)
  · intro common path member
    exact common path ((SourceEmptinessClassFold.mem_seededPaths paths path).mp member)

/-- The actual rotated fold inputs share one proper subtree of the original parent. -/
theorem class_rotated_common (term : Term Symbol) (paths : Class) (active : Nontrivial paths)
    (satisfied : ClassSat term paths) :
    ∃ part, (∀ path ∈ paths.map (List.map Int.ofNat), SymbolicSignedPaths.lookup term path = some part) ∧
      (∀ path ∈ SourceEmptinessClassFold.seededPaths (paths.map (List.map Int.ofNat)),
        SymbolicSignedPaths.lookup term path = some part) ∧ part.height < term.height := by
  obtain ⟨part, common, smaller⟩ := class_signed_common term paths active satisfied
  exact ⟨part, common, (rotated_common term _ part).mpr common, smaller⟩

end MicroCFTA.SourceCurrentConjunctionClassWitness
