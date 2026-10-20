import MicroCFTA.SourceCurrentStoredLiteralRowLineage
import MicroCFTA.InternedStoredLeafShape
import MicroCFTA.InternedStoredSubstitutionScope
import MicroCFTA.SourceCurrentRecursiveHeadRowOrigins

/-!
# Exact native self-substitution capture slots

A row-bearing mapped leaf is the same closed leaf or the complete Mu that
replaces the selected own reference. Every other reference stays literal.
-/
namespace MicroCFTA.SourceCurrentNativeSelfCaptureSlots
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedStoredSubstitution (leaves input slot)
open InternedBinderProtocol (NodeKey)
open SourceCurrentRecursiveHeadRowOrigins (selfEnvironment)
open SourceCurrentStoredLiteralRowLineage (RowAt)

/-- A row-bearing mapped lookup retains the exact closed leaf or exact complete self Mu at that slot. -/
theorem lookup (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (index : Nat) (captured : Value Symbol Guard)
    (found : ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[index]? = some captured)
    (row : EdgeValue Symbol Guard) (inside : RowAt captured row) :
    (∃ leaf, (leaves body)[index]? = some leaf ∧ leaf.free = [] ∧ captured = leaf ∧ RowAt leaf row) ∨
    ((leaves body)[index]? = some (.reference (.interned entry.identity)) ∧
      captured = .mu entry body depth ordinary) := by
  cases selected : (leaves body)[index]? with
  | none =>
      simp only [List.getElem?_map,selected,Option.map_none] at found
      cases found
  | some leaf =>
      have mapped : input (selfEnvironment entry body depth ordinary) leaf = captured := by
        simpa only [List.getElem?_map,selected,Option.map_some,Option.some.injEq] using found
      rcases InternedStoredLeafShape.leaves_shape body leaf (List.mem_of_getElem? selected) with closed | ⟨name,rfl⟩
      · have same : captured = leaf := mapped.symm.trans
          (InternedStoredSubstitutionScope.input_closed leaf _ closed)
        exact .inl ⟨leaf,rfl,closed,same,same ▸ inside⟩
      · by_cases own : name = .interned entry.identity
        · refine .inr ⟨by simp only [own],?_⟩
          simpa only [input,selfEnvironment,own,ite_true,Option.getD_some] using mapped.symm
        · have same : captured = .reference name := by
            simpa only [input,selfEnvironment,own,ite_false,Option.getD_none] using mapped.symm
          rw [same] at inside
          cases inside

/-- Canonical identity lookup gives the same split when its coherent available source premises hold. -/
theorem canonical_slot (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (available : InternedNestedProvenance.Values state (leaves body))
    (leaf : Value Symbol Guard) (member : leaf ∈ leaves body)
    (row : EdgeValue Symbol Guard)
    (inside : RowAt (input (selfEnvironment entry body depth ordinary) leaf) row) :
    (∃ original, (leaves body)[slot (leaves body) leaf]? = some original ∧ original.free = [] ∧
      input (selfEnvironment entry body depth ordinary) leaf = original ∧ RowAt original row) ∨
    ((leaves body)[slot (leaves body) leaf]? = some (.reference (.interned entry.identity)) ∧
      input (selfEnvironment entry body depth ordinary) leaf = .mu entry body depth ordinary) := by
  have selected := InternedStoredSubstitutionScope.slot_lookup (leaves body) leaf state coherent available member
  have found : ((leaves body).map (input (selfEnvironment entry body depth ordinary)))[slot (leaves body) leaf]? =
      some (input (selfEnvironment entry body depth ordinary) leaf) := by
    simp only [List.getElem?_map,selected,Option.map_some]
  exact lookup entry body depth ordinary (slot (leaves body) leaf)
    (input (selfEnvironment entry body depth ordinary) leaf) found row inside

end MicroCFTA.SourceCurrentNativeSelfCaptureSlots

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentNativeSelfCaptureSlots.lookup
#print MicroCFTA.SourceCurrentNativeSelfCaptureSlots.lookup
#print axioms MicroCFTA.SourceCurrentNativeSelfCaptureSlots.lookup
#check @MicroCFTA.SourceCurrentNativeSelfCaptureSlots.canonical_slot
#print MicroCFTA.SourceCurrentNativeSelfCaptureSlots.canonical_slot
#print axioms MicroCFTA.SourceCurrentNativeSelfCaptureSlots.canonical_slot
