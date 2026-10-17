import MicroCFTA.SourceCurrentLiteralFilterParts
import MicroCFTA.SourceCurrentOpenObservationSurvival

/-!
# Exact root parts determine open observations

Literal Mu atoms retain their complete values. Exact ordinary rows retain
all symbols, guards, and ordered children. Available normal roots also
have physical Empty agreement. The view heap can be arbitrary.
-/
namespace MicroCFTA.SourceCurrentLiteralPartsObservations
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedStoredMuOrigins (Normal)
open InternedUnionNormalForm (Atomic)
open SourceCurrentLiteralRootParts (Literal Row SameParts)
open SourceCurrentOpenObservations (ReferenceOrigin Same)
open SourceCurrentOpenObservationSurvival (Related)
open MergedFreshOrdinaryGraph (Origin)

private theorem no_reference [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (name : InternedBinderProtocol.Reference) :
    ¬ ReferenceOrigin view [] name := by
  intro present
  obtain ⟨_,member,_⟩ := (SourceCurrentOpenObservations.reference_seeds view [] name).mp present
  cases member

private theorem atomic_reference [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (value : Value Symbol Guard) (atomic : Atomic value)
    (name : InternedBinderProtocol.Reference) :
    ReferenceOrigin view [value] name ↔ ∃ atom, Literal value atom ∧ ReferenceOrigin view [atom] name := by
  cases value with
  | empty =>
      have none := SourceCurrentOpenObservations.reference_expand view
        (.empty : Value Symbol Guard) (by intro name impossible; cases impossible) name
      exact iff_of_false (fun found => no_reference view name (none.mp found))
        (by rintro ⟨atom,part,_⟩; cases part)
  | node entry rows level free =>
      have none := SourceCurrentOpenObservations.reference_expand view
        (.node entry rows level free) (by intro name impossible; cases impossible) name
      exact iff_of_false (fun found => no_reference view name (none.mp found))
        (by rintro ⟨atom,part,_⟩; cases part)
  | reference own =>
      constructor
      · intro actual; exact ⟨_,.reference own,actual⟩
      · rintro ⟨atom,part,actual⟩; cases part; exact actual
  | mu entry body depth ordinary =>
      constructor
      · intro actual; exact ⟨_,.mu entry body depth ordinary,actual⟩
      · rintro ⟨atom,part,actual⟩; cases part; exact actual
  | union => cases atomic

private theorem atomic_row [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (value : Value Symbol Guard) (atomic : Atomic value)
    (row : EdgeValue Symbol Guard) :
    Origin view [value] row ↔ Row value row ∨ ∃ atom, Literal value atom ∧ Origin view [atom] row := by
  cases value with
  | empty =>
      exact iff_of_false (MergedFreshOrdinaryGraph.origin_empty view row)
        (by rintro (part | ⟨atom,part,_⟩) <;> cases part)
  | node entry rows level free =>
      constructor
      · intro actual
        exact Or.inl (.node ((MergedFreshOrdinaryGraph.origin_node view entry rows level free row).mp actual))
      · rintro (part | ⟨atom,part,_⟩)
        · cases part with
          | node member => exact (MergedFreshOrdinaryGraph.origin_node view entry rows level free row).mpr member
        · cases part
  | reference own =>
      constructor
      · intro actual; exact Or.inr ⟨_,.reference own,actual⟩
      · rintro (part | ⟨atom,part,actual⟩)
        · cases part
        · cases part; exact actual
  | mu entry body depth ordinary =>
      constructor
      · intro actual; exact Or.inr ⟨_,.mu entry body depth ordinary,actual⟩
      · rintro (part | ⟨atom,part,actual⟩)
        · cases part
        · cases part; exact actual
  | union => cases atomic

private theorem references [DecidableEq (EdgeKey Symbol Guard)]
    (common view : State Symbol Guard) (normal : Normal common)
    (value : Value Symbol Guard) (available : Available common value)
    (name : InternedBinderProtocol.Reference) :
    ReferenceOrigin view [value] name ↔ ∃ atom, Literal value atom ∧ ReferenceOrigin view [atom] name := by
  cases value with
  | empty | reference | node | mu => apply atomic_reference; trivial
  | union entry members level free =>
      have flat := InternedUnionNormalForm.resident_flat common normal.flat _ available.resident
      have expand := SourceCurrentOpenObservations.reference_expand view (.union entry members level free)
        (by intro name impossible; cases impossible) name
      rw [expand,SourceCurrentOpenObservations.reference_seeds]
      constructor
      · rintro ⟨member,present,actual⟩
        obtain ⟨atom,part,found⟩ := (atomic_reference view member (flat member present) name).mp actual
        exact ⟨atom,.union present part,found⟩
      · rintro ⟨atom,part,actual⟩
        obtain ⟨member,present,inside⟩ := (SourceCurrentLiteralRootParts.literal_union entry members level free atom).mp part
        exact ⟨member,present,(atomic_reference view member (flat member present) name).mpr ⟨atom,inside,actual⟩⟩

private theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    (common view : State Symbol Guard) (normal : Normal common)
    (value : Value Symbol Guard) (available : Available common value) (row : EdgeValue Symbol Guard) :
    Origin view [value] row ↔ Row value row ∨ ∃ atom, Literal value atom ∧ Origin view [atom] row := by
  cases value with
  | empty | reference | node | mu => apply atomic_row; trivial
  | union entry members level free =>
      have flat := InternedUnionNormalForm.resident_flat common normal.flat _ available.resident
      rw [MergedFreshOrdinaryGraph.origin_union]
      constructor
      · rintro ⟨member,present,actual⟩
        rcases (atomic_row view member (flat member present) row).mp actual with part | ⟨atom,part,found⟩
        · exact Or.inl (.union present part)
        · exact Or.inr ⟨atom,.union present part,found⟩
      · rintro (part | ⟨atom,part,actual⟩)
        · obtain ⟨member,present,inside⟩ := (SourceCurrentLiteralRootParts.row_union entry members level free row).mp part
          exact ⟨member,present,(atomic_row view member (flat member present) row).mpr (Or.inl inside)⟩
        · obtain ⟨member,present,inside⟩ := (SourceCurrentLiteralRootParts.literal_union entry members level free atom).mp part
          exact ⟨member,present,(atomic_row view member (flat member present) row).mpr (Or.inr ⟨atom,inside,actual⟩)⟩

private theorem atomic_nonempty (common : State Symbol Guard) (normal : Normal common)
    (value : Value Symbol Guard) (available : Available common value) (atomic : Atomic value)
    (nonempty : value.referenceOf ≠ .empty) :
    (∃ atom, Literal value atom) ∨ ∃ row, Row value row := by
  cases value with
  | empty => exact False.elim (nonempty rfl)
  | reference name => exact Or.inl ⟨_,.reference name⟩
  | mu entry body depth ordinary => exact Or.inl ⟨_,.mu entry body depth ordinary⟩
  | union => cases atomic
  | node entry rows level free =>
      have proper := InternedNonemptyRecords.resident_nonempty common normal.proper _ available.resident
      obtain ⟨row,member⟩ := List.exists_mem_of_ne_nil rows proper
      exact Or.inr ⟨row,.node member⟩

private theorem no_parts_empty (common : State Symbol Guard) (normal : Normal common)
    (value : Value Symbol Guard) (available : Available common value)
    (noAtoms : ∀ atom, ¬ Literal value atom) (noRows : ∀ row, ¬ Row value row) :
    value.referenceOf = .empty := by
  by_cases nonempty : value.referenceOf = .empty
  · exact nonempty
  apply False.elim
  cases value with
  | empty | reference | node | mu =>
      rcases atomic_nonempty common normal _ available trivial nonempty with ⟨atom,part⟩ | ⟨row,part⟩
      · exact noAtoms atom part
      · exact noRows row part
  | union entry members level free =>
      have proper := InternedNonemptyRecords.resident_nonempty common normal.proper _ available.resident
      have hasMember : members ≠ [] := by intro same; simp only [same,List.length_nil] at proper; omega
      obtain ⟨member,present⟩ := List.exists_mem_of_ne_nil members hasMember
      have flat := InternedUnionNormalForm.resident_flat common normal.flat _ available.resident
      have live := InternedUnionNonemptyMembers.resident_membersNonempty common normal.members _ available.resident
      rcases atomic_nonempty common normal member (available.children member present) (flat member present)
        (live member present) with ⟨atom,part⟩ | ⟨row,part⟩
      · exact noAtoms atom (.union present part)
      · exact noRows row (.union present part)

/-- Equal literal atoms and complete rows give every finite observation in any common view. -/
theorem same [DecidableEq (EdgeKey Symbol Guard)]
    (firstState secondState : State Symbol Guard) (firstNormal : Normal firstState) (secondNormal : Normal secondState)
    (first second : Value Symbol Guard) (firstAvailable : Available firstState first)
    (secondAvailable : Available secondState second) (parts : SameParts first second)
    (depth : Nat) (view : State Symbol Guard) : Same depth view [first] [second] := by
  apply SourceCurrentOpenObservations.of_origins depth view [first] [second]
  · intro name
    rw [references firstState view firstNormal first firstAvailable name,
      references secondState view secondNormal second secondAvailable name]
    constructor
    · rintro ⟨atom,part,actual⟩; exact ⟨atom,(parts.1 atom).mp part,actual⟩
    · rintro ⟨atom,part,actual⟩; exact ⟨atom,(parts.1 atom).mpr part,actual⟩
  · intro row
    rw [rows firstState view firstNormal first firstAvailable row,
      rows secondState view secondNormal second secondAvailable row]
    constructor
    · rintro (part | ⟨atom,part,actual⟩)
      · exact Or.inl ((parts.2 row).mp part)
      · exact Or.inr ⟨atom,(parts.1 atom).mp part,actual⟩
    · rintro (part | ⟨atom,part,actual⟩)
      · exact Or.inl ((parts.2 row).mpr part)
      · exact Or.inr ⟨atom,(parts.1 atom).mpr part,actual⟩

/-- Available normal roots with the same exact parts also agree on physical Empty. -/
theorem related [DecidableEq (EdgeKey Symbol Guard)]
    (firstState secondState : State Symbol Guard) (firstNormal : Normal firstState) (secondNormal : Normal secondState)
    (first second : Value Symbol Guard) (firstAvailable : Available firstState first)
    (secondAvailable : Available secondState second) (parts : SameParts first second) : Related first second := by
  constructor
  · constructor
    · intro empty
      have shape := InternedEmptyNormalization.reference_empty first |>.mp empty
      subst first
      exact no_parts_empty secondState secondNormal second secondAvailable
        (fun atom part => by have absent := (parts.1 atom).mpr part; cases absent)
        (fun row part => by have absent := (parts.2 row).mpr part; cases absent)
    · intro empty
      have shape := InternedEmptyNormalization.reference_empty second |>.mp empty
      subst second
      exact no_parts_empty firstState firstNormal first firstAvailable
        (fun atom part => by have absent := (parts.1 atom).mp part; cases absent)
        (fun row part => by have absent := (parts.2 row).mp part; cases absent)
  · exact same firstState secondState firstNormal secondNormal first second firstAvailable secondAvailable parts

end MicroCFTA.SourceCurrentLiteralPartsObservations
