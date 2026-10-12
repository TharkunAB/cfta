import MicroCFTA.PruneCandidates

/-!
# Preserve guards when actual identities are ambiguous

Sparse substitution can use distinct fresh names where a complete term uses
one ambient name. Nested scopes can then change the query. The source keeps
the complete original guard before it uses such a sparse decision.
-/
namespace MicroCFTA.PruneAmbiguity
open PruneSchedule PruneCandidates

/-- A successful pass with any ambiguous candidate restores the complete edge. -/
theorem successful_ambiguity_restores (original : Edge) (candidates : List (Candidate Edge))
    (ambiguous : ∃ candidate ∈ candidates, candidate.ambiguous = true)
    (result : List Edge) (success : check original [] (candidates.map protect) = .ok result) :
    result = [original] := by
  rcases check_success_cases original [] (candidates.map protect) result success with restored | ⟨_, complete⟩
  · exact restored
  · obtain ⟨candidate, member, unknownIdentity⟩ := ambiguous
    have impossible := complete (protect candidate) (List.mem_map.mpr ⟨candidate, member, rfl⟩)
    exact False.elim (impossible (by simp [protect, safeVerdict, unknownIdentity]))

/-- Only unambiguous decisions need a language proof after the repaired gate. -/
theorem check_exact (meaning cell : Edge → Term → Prop) (original : Edge)
    (candidates : List (Candidate Edge))
    (cover : ∀ term, (∃ candidate ∈ candidates, cell candidate.edge term) ↔ meaning original term)
    (yes : ∀ candidate ∈ candidates, candidate.ambiguous = false → candidate.verdict = .yes →
      ∀ term, meaning candidate.edge term ↔ cell candidate.edge term)
    (no : ∀ candidate ∈ candidates, candidate.ambiguous = false → candidate.verdict = .no →
      ∀ term, ¬cell candidate.edge term)
    (result : List Edge) (success : check original [] (candidates.map protect) = .ok result)
    (term : Term) : Denotes meaning result term ↔ meaning original term := by
  apply PruneCandidates.check_exact meaning (fun candidate term => cell candidate.edge term)
    original (candidates.map protect) ?_ ?_ ?_ result success term
  · intro term
    have members : (∃ candidate ∈ candidates.map protect, cell candidate.edge term) ↔
        ∃ candidate ∈ candidates, cell candidate.edge term := by
      constructor
      · rintro ⟨candidate, member, accepted⟩
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact ⟨original, present, accepted⟩
      · rintro ⟨candidate, member, accepted⟩
        exact ⟨protect candidate, List.mem_map.mpr ⟨candidate, member, rfl⟩, accepted⟩
    exact members.trans (cover term)
  · intro candidate member proved term
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨known, proved⟩ := (safeVerdict_yes _ _).mp proved
    exact yes original present known proved term
  · intro candidate member disproved term
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨known, disproved⟩ := (safeVerdict_no _ _).mp disproved
    exact no original present known disproved term

/-- The historical loop accepts a sparse Yes even when identity is ambiguous. -/
theorem old_discharges_ambiguous_yes :
    check (0 : Nat) [] [⟨1, .yes, true⟩] = .ok [1] := rfl

/-- The new gate retains the original guarded edge for the same candidate. -/
theorem repaired_retains_ambiguous_yes :
    check (0 : Nat) [] ([⟨1, .yes, true⟩].map protect) = .ok [0] := rfl

end MicroCFTA.PruneAmbiguity
