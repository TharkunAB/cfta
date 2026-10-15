import MicroCFTA.SourceEqualityOnePassGraph

/-!
# Actual source guards at the independent equality language

The contradiction branch rejects every term satisfying both input payloads.
The live branch retains exactly the original own classes in physical source
order. Original record validity therefore supplies every selected class law.
-/
namespace MicroCFTA.SourceEqualityOnePassPrecheck
open Language EqualityNormalize SourceEqualityClassOrder SourceEqualityPrecheck

/-- A physical source payload retains coherent nontrivial classes whenever it is noncontradictory. -/
def Valid (input : Constraint) : Prop :=
  ∀ records, input = some records → ∀ record ∈ records, Coherent record ∧ Nontrivial record.paths

/-- Combined contradiction cannot occur on a term satisfying both actual source payloads. -/
theorem contradiction_rejects {own inherited : Constraint} (actual : precheck own inherited = .ok .emptyChildren) (term : Term Symbol) :
    ¬ (Sat term own ∧ Sat term inherited) := by
  intro satisfied
  have combined := (combine_exact own inherited term).mpr satisfied
  unfold precheck at actual
  split at actual
  · cases actual
  · split at actual
    · rename_i rejected
      have contradiction : combine own inherited = .contradiction := by
        cases result : combine own inherited <;> simp_all [rejects]
      simp only [contradiction, RunSat] at combined
    · cases own with
      | none => simp [unsafeOrdered, Except.map] at actual
      | some records => simp [unsafeOrdered, Except.map] at actual

/-- Actual live ordering retains every physical class validity premise. -/
theorem live_valid {own inherited : Constraint} {records : List Record}
    (actual : precheck own inherited = .ok (.classes records)) (valid : Valid own) :
    ∀ record ∈ records, Coherent record ∧ Nontrivial record.paths := by
  obtain ⟨original, payload, rfl, _⟩ := live_payload own inherited records actual
  intro record member
  exact valid original payload record ((ordered_perm original).mem_iff.mp member)

/-- Every original own equality remains satisfied in the actual live physical class order. -/
theorem live_satisfied {own inherited : Constraint} {records : List Record}
    (actual : precheck own inherited = .ok (.classes records)) (term : Term Symbol) (satisfied : Sat term own) :
    Satisfies term (records.map Record.paths) := by
  obtain ⟨original, payload, rfl, _⟩ := live_payload own inherited records actual
  rw [payload] at satisfied
  intro paths member
  obtain ⟨record, included, rfl⟩ := List.mem_map.mp member
  exact satisfied record.paths (List.mem_map.mpr ⟨record, (ordered_perm original).mem_iff.mp included, rfl⟩)

end MicroCFTA.SourceEqualityOnePassPrecheck
