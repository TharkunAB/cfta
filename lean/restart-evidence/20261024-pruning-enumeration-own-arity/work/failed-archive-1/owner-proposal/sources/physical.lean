import MicroCFTA.SourceEqualityGuardReadback
import MicroCFTA.SourceEqualityOnePassPrecheck

/-!
# Physical class records from the actual source equality accessor

Each source class builds its trie and sorted path set. Completed source
normalization derives successful construction and every pass invariant.
The physical payload has the same independent equality meaning.
-/
namespace MicroCFTA.SourceEqualityPhysicalPayload
open Language EqualityNormalize SourceEqualityClassOrder SourceEqualityGuardReadback
open SourceObservations SourceGuards SourceSymbolicIndex SourceCompactGuards

/-- Read source equality classes as physical records, with the actual malformed-trie failure. -/
def read : Option Constraints → Except String SourceEqualityPrecheck.Constraint
  | none => .ok none
  | some classes => match recordsOf classes with
    | none => .error "toPathTrie: input paths must be distinct, with none a prefix of another"
    | some records => .ok (some records)

/-- The source edge accessor builds physical records from its actual complete constraint. -/
noncomputable def own (constraint : Constraint Formula) : Except String SourceEqualityPrecheck.Constraint :=
  read (sourceEqualities constraint)

/-- Actual normalized classes derive successful record construction, exact paths, and valid tries. -/
theorem normal_records (classes : Constraints) (normal : NormalClasses classes) :
    ∃ records, recordsOf classes = some records ∧
      (∀ record ∈ records, Coherent record ∧ Nontrivial record.paths) ∧ records.map Record.paths = classes := by
  obtain ⟨records, built, coherent, paths⟩ := recordsOf_complete classes (consistent_supported classes normal.2.1)
  have same : records.map Record.paths = classes := paths.trans
    ((List.map_congr_left (fun paths member => normal.2.2 paths member)).trans (List.map_id classes))
  refine ⟨records, built, ?_, same⟩
  intro record member
  exact ⟨coherent record member, normal.1 record.paths (same ▸ List.mem_map.mpr ⟨record, member, rfl⟩)⟩

/-- Every source payload from completed normalization has a finite exact physical readback. -/
theorem complete (equalities : Option Constraints) (cached : Cached equalities) :
    ∃ payload, read equalities = .ok payload ∧ SourceEqualityOnePassPrecheck.Valid payload ∧
      ∀ term : Term Symbol, SourceEqualityPrecheck.Sat term payload ↔ Sat term equalities := by
  cases equalities with
  | none => exact ⟨none, rfl, by simp [SourceEqualityOnePassPrecheck.Valid], fun _ => Iff.rfl⟩
  | some classes =>
      obtain ⟨records, built, valid, paths⟩ := normal_records classes (cached classes rfl)
      refine ⟨some records, by simp only [read, built], ?_, ?_⟩
      · intro other same
        cases same
        exact valid
      · intro term
        simp only [SourceEqualityPrecheck.Sat, Sat, paths]

/-- Actual Constraint.equalities derives valid physical records and all required own class facts. -/
theorem own_complete [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (stored : Cached constraint.equalities) :
    ∃ payload, own constraint = .ok payload ∧ SourceEqualityOnePassPrecheck.Valid payload ∧
      (∀ term : Term (Label Formula), SourceEqualityPrecheck.Sat term payload ↔ Sat term (sourceEqualities constraint)) ∧
      ∀ term : Term (Label Formula), acceptsConstraint formulas solver constraint term = true → SourceEqualityPrecheck.Sat term payload := by
  obtain ⟨payload, built, valid, exact⟩ := complete (Symbol := Label Formula) (sourceEqualities constraint) (source_cached constraint stored)
  exact ⟨payload, built, valid, exact, fun term accepted =>
    (exact term).mpr (accepted_sat formulas solver constraint (active stored) term accepted)⟩

end MicroCFTA.SourceEqualityPhysicalPayload
