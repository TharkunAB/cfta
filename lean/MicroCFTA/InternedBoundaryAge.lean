import MicroCFTA.InternedBoundaryAtoms
import MicroCFTA.InternedNodeIdentityFootprint

/-!
# Reservation ages of reference and Mu boundaries

Every interned boundary identity occurs in the complete record footprint.
Old completed probe records therefore exclude later reference and Mu
boundaries, even when ordinary normalization removes intermediate nodes.
-/
namespace MicroCFTA.InternedBoundaryAge
open InternedConstructorTemplates InternedProbeProvenance
open InternedBoundaryAtoms InternedNodeIdentityFootprint
open InternedBinderProtocol (NodeRef)

/-- Each interned reference or Mu boundary has its exact identity in the complete footprint. -/
theorem atom_occurs (value : Value Symbol Guard) (item : NodeRef) (identity : Nat)
    (kind : item = .ref (.interned identity) ∨ item = .mu identity)
    (member : item ∈ atoms value) : Occurs identity value := by
  cases value with
  | empty => simp only [atoms, List.not_mem_nil] at member
  | reference name =>
      simp only [atoms] at member
      have same : item = .ref name := List.mem_singleton.mp member
      rw [same] at kind
      rcases kind with sameName | impossible
      · cases NodeRef.ref.inj sameName
        exact .reference
      · cases impossible
  | node entry edges depth free =>
      simp only [atoms] at member
      obtain ⟨edge, edgeMember, child, childMember, occurrence⟩ := (edge_member edges item).mp member
      exact .child (.node entry edges depth free) child (List.mem_flatMap.mpr ⟨edge, edgeMember, childMember⟩)
        (atom_occurs child item identity kind occurrence)
  | union entry members depth free =>
      simp only [atoms] at member
      obtain ⟨child, childMember, occurrence⟩ := (many_member members item).mp member
      exact .child (.union entry members depth free) child childMember
        (atom_occurs child item identity kind occurrence)
  | mu entry body depth ordinary =>
      simp only [atoms] at member
      have same : item = .mu entry.identity := List.mem_singleton.mp member
      rw [same] at kind
      rcases kind with impossible | sameIdentity
      · cases impossible
      · exact .entry (.mu entry body depth ordinary) entry rfl (NodeRef.mu.inj sameIdentity)
termination_by sizeOf value
decreasing_by
  · have edgeSmall := List.sizeOf_lt_of_mem edgeMember
    cases edge with
    | mk stored children =>
        have childSmall := List.sizeOf_lt_of_mem childMember
        simp only [EdgeValue.children] at childSmall
        simp_wf
        simp only [EdgeValue.mk.sizeOf_spec] at edgeSmall
        subst value
        simp only [Value.node.sizeOf_spec]
        omega
  · have childSmall := List.sizeOf_lt_of_mem childMember
    simp_wf
    subst value
    simp only [Value.union.sizeOf_spec]
    omega

/-- A completed old record contains no reference or Mu boundary allocated at or after its cutoff. -/
theorem old_absent (value : Value Symbol Guard) (cutoff : Nat)
    (old : ∀ identity, Occurs identity value → identity < cutoff)
    (identity : Nat) (new : cutoff ≤ identity) :
    .ref (.interned identity) ∉ atoms value ∧ .mu identity ∉ atoms value := by
  constructor
  · intro member
    have earlier := old identity (atom_occurs value _ identity (Or.inl rfl) member)
    omega
  · intro member
    have earlier := old identity (atom_occurs value _ identity (Or.inr rfl) member)
    omega

end MicroCFTA.InternedBoundaryAge
