import MicroCFTA.InternedRootProfileLists
import MicroCFTA.InternedBoundaryProvenance

/-!
# Actual root profile names retain free-reference provenance

Every literal root profile member is a boundary reference of the actual
record. Source coherence then places it in the record's stored free set.
Actual reservation freshness therefore applies to the pure callback form.
-/
namespace MicroCFTA.InternedProfileFree
open InternedConstructorTemplates InternedRootProfile InternedRootProfileLists
open InternedBoundaryAtoms InternedBoundaryProvenance InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)

/-- Every root profile name is an actual boundary reference. -/
theorem member_boundary (value : Value Symbol Guard) (name : Reference)
    (member : name ∈ (profile value).getD []) : .ref name ∈ atoms value := by
  cases value with
  | empty | node | mu => simp [profile] at member
  | reference other => simpa [profile, atoms] using member
  | union entry members depth free =>
      cases computed : many members with
      | none => simp [profile, computed] at member
      | some names =>
          have present : name ∈ names := by simpa [profile, computed] using member
          obtain ⟨child, included, childMember⟩ := (many_some_member members names computed name).mp present
          have occurrence := member_boundary child name childMember
          simpa only [atoms] using (many_member members (.ref name)).mpr ⟨child, included, occurrence⟩
termination_by sizeOf value
decreasing_by
  have smaller := List.sizeOf_lt_of_mem included
  simp_wf
  simp_all
  omega

/-- Each actual root profile name occurs in the coherent stored free set. -/
theorem member_free (value : Value Symbol Guard) (name : Reference) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (member : name ∈ (profile value).getD []) : name ∈ value.free :=
  ref_free name value state coherent available (member_boundary value name member)

end MicroCFTA.InternedProfileFree
