import MicroCFTA.InternedBoundaryFilter
import MicroCFTA.InternedFreeOccurrenceRank

/-!
# Actual payload provenance for boundary identities

A Mu boundary identifies an available complete Mu record. A reference
boundary is exactly an occurrence with no enclosing Mu. These facts relate
the normalization profile to resident payloads and actual free variables.
-/
namespace MicroCFTA.InternedBoundaryProvenance
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBoundaryAtoms InternedFreeOccurrenceRank
open InternedBinderProtocol (Reference NodeKey)

mutual
/-- Each Mu boundary belongs to an actual complete resident payload. -/
theorem mu_available (value : Value Symbol Guard) (state : State Symbol Guard) (available : Available state value)
    (identity : Nat) (present : .mu identity ∈ atoms value) :
    ∃ entry body depth ordinary, entry.identity = identity ∧ Available state (.mu entry body depth ordinary) := by
  cases value with
  | empty | reference => simp [atoms] at present
  | mu entry body depth ordinary =>
      have same : identity = entry.identity := by simpa [atoms] using present
      exact ⟨entry, body, depth, ordinary, same.symm, available⟩
  | node entry edges depth free =>
      exact edges_mu_available edges state (fun child member => available.children child member) identity
        (by simpa only [atoms] using present)
  | union entry members depth free =>
      exact many_mu_available members state (fun child member => available.children child member) identity
        (by simpa only [atoms] using present)
termination_by sizeOf value

/-- Ordered available children supply every Mu boundary in their combined profile. -/
theorem many_mu_available (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (available : ∀ value ∈ values, Available state value) (identity : Nat) (present : .mu identity ∈ manyAtoms values) :
    ∃ entry body depth ordinary, entry.identity = identity ∧ Available state (.mu entry body depth ordinary) := by
  cases values with
  | nil => simp [manyAtoms] at present
  | cons first rest =>
      simp only [manyAtoms, List.mem_append] at present
      rcases present with head | tail
      · exact mu_available first state (available first (by simp)) identity head
      · exact many_mu_available rest state (fun value member => available value (by simp [member])) identity tail
termination_by sizeOf values

/-- Original ordered edge children supply every Mu boundary of an ordinary record. -/
theorem edges_mu_available (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (identity : Nat) (present : .mu identity ∈ edgeAtoms edges) :
    ∃ entry body depth ordinary, entry.identity = identity ∧ Available state (.mu entry body depth ordinary) := by
  cases edges with
  | nil => simp [edgeAtoms] at present
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [edgeAtoms, List.mem_append] at present
          rcases present with head | tail
          · exact many_mu_available children state
              (fun value member => available value (by simp [EdgeValue.children, member])) identity head
          · exact edges_mu_available rest state
              (fun value member => available value (by simp [EdgeValue.children, member])) identity tail
termination_by sizeOf edges
end

mutual
/-- Literal boundary references are precisely free-reference occurrences with zero Mu cost. -/
theorem ref_zero (name : Reference) (value : Value Symbol Guard) :
    .ref name ∈ atoms value ↔ (name, 0) ∈ costs value := by
  cases value with
  | empty | reference => simp [atoms, costs]
  | node entry edges depth free => simpa only [atoms, costs] using edges_ref_zero name edges
  | union entry members depth free => simpa only [atoms, costs] using many_ref_zero name members
  | mu entry body depth ordinary => simp [atoms, costs]
termination_by sizeOf value

/-- Ordered member boundary references retain zero cost. -/
theorem many_ref_zero (name : Reference) (values : List (Value Symbol Guard)) :
    .ref name ∈ manyAtoms values ↔ (name, 0) ∈ manyCosts values := by
  cases values with
  | nil => simp [manyAtoms, manyCosts]
  | cons first rest => simp only [manyAtoms, manyCosts, List.mem_append, ref_zero name first, many_ref_zero name rest]
termination_by sizeOf values

/-- Ordinary edge boundaries add no Mu frame to a literal reference occurrence. -/
theorem edges_ref_zero (name : Reference) (edges : List (EdgeValue Symbol Guard)) :
    .ref name ∈ edgeAtoms edges ↔ (name, 0) ∈ edgeCosts edges := by
  cases edges with
  | nil => simp [edgeAtoms, edgeCosts]
  | cons first rest =>
      cases first with
      | mk entry children => simp only [edgeAtoms, edgeCosts, List.mem_append, many_ref_zero name children, edges_ref_zero name rest]
termination_by sizeOf edges
end

/-- A boundary reference is free in the actual source record. -/
theorem ref_free (name : Reference) (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (present : .ref name ∈ atoms value) : name ∈ value.free :=
  (costs_free value state coherent available name).mp ⟨0, (ref_zero name value).mp present⟩

/-- A boundary Mu identity selects a complete payload in the actual node table. -/
theorem mu_stored (value : Value Symbol Guard) (state : State Symbol Guard) (available : Available state value)
    (identity : Nat) (present : .mu identity ∈ atoms value) :
    ∃ entry body depth ordinary, entry.identity = identity ∧ state.nodeRecords entry.key = some (.mu entry body depth ordinary) := by
  obtain ⟨entry, body, depth, ordinary, same, resident⟩ := mu_available value state available identity present
  exact ⟨entry, body, depth, ordinary, same, resident.resident entry rfl⟩

end MicroCFTA.InternedBoundaryProvenance
