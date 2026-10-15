import MicroCFTA.SourceEqualityPartialConstraintKey
import MicroCFTA.SourceEqualityDescend

/-!
# Exact physical payload equality from trie keys

Coherent records store canonical path lists. Their trie fields therefore
determine both record fields. Ordered physical keys determine complete
well-formed payloads, including the contradiction tag.
-/
namespace MicroCFTA.SourceEqualityPhysicalPayloadCanonical
open EqualityNormalize SourceEqualityClassOrder SourceEqualityPartialConstraintKey

/-- Equal tries determine the complete coherent class records. -/
theorem record_eq_of_trie (first second : Record) (firstCoherent : Coherent first)
    (secondCoherent : Coherent second) (same : first.trie = second.trie) : first = second := by
  have paths := canonicalClass_ext first.paths second.paths (fun path =>
    (firstCoherent.2.2 path).symm.trans (same ▸ secondCoherent.2.2 path))
  rw [firstCoherent.2.1, secondCoherent.2.1] at paths
  cases first
  cases second
  cases same
  cases paths
  rfl

/-- The ordered trie key determines every coherent record occurrence. -/
theorem records_eq_of_key (first second : List Record)
    (firstCoherent : ∀ record ∈ first, Coherent record)
    (secondCoherent : ∀ record ∈ second, Coherent record)
    (same : key first = key second) : first = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons _ _ => simp [key] at same
  | cons first rest ih =>
      cases second with
      | nil => simp [key] at same
      | cons second remaining =>
          change first.trie :: key rest = second.trie :: key remaining at same
          have equal := List.cons.inj same
          have heads := record_eq_of_trie first second (firstCoherent _ List.mem_cons_self)
            (secondCoherent _ List.mem_cons_self) equal.1
          have tails := ih remaining (fun record member => firstCoherent record (List.mem_cons_of_mem _ member))
            (fun record member => secondCoherent record (List.mem_cons_of_mem _ member)) equal.2
          rw [heads, tails]

/-- Equal tagged keys determine complete well-formed physical payloads. -/
theorem eq_of_key (first second : SourceEqualityPrecheck.Constraint)
    (firstWellFormed : SourceEqualityDescend.WellFormed first)
    (secondWellFormed : SourceEqualityDescend.WellFormed second)
    (same : first.map key = second.map key) : first = second := by
  cases first with
  | none => cases second <;> simp_all
  | some first =>
      cases second with
      | none => simp at same
      | some second =>
          exact congrArg some (records_eq_of_key first second
            (fun record member => (firstWellFormed first rfl record member).1)
            (fun record member => (secondWellFormed second rfl record member).1) (Option.some.inj same))

/-- Well-formed payload equality is exactly tagged physical-key equality. -/
theorem key_eq_iff (first second : SourceEqualityPrecheck.Constraint)
    (firstWellFormed : SourceEqualityDescend.WellFormed first)
    (secondWellFormed : SourceEqualityDescend.WellFormed second) :
    first.map key = second.map key ↔ first = second :=
  ⟨eq_of_key first second firstWellFormed secondWellFormed, congrArg (Option.map key)⟩

end MicroCFTA.SourceEqualityPhysicalPayloadCanonical
