import MicroCFTA.SourceEqualityDescend
import MicroCFTA.SourceEqualityPCSGuard

/-!
# Actual combined and descended inherited equality payloads

Physical source records supply ascending tries from their actual constructor.
The source combiner runs its terminating array normalizer. Readback derives
coherent records and exact conjunction. Actual child descent then retains the
same physical representation and the parent's satisfied equality obligations.
-/
namespace MicroCFTA.SourceEqualityInheritedPayload
open Language EqualityNormalize SourceEqualityClassOrder SourceEqualityGuardReadback
open SourceEqualityDescend (WellFormed)

/-- Read the ordered class path sets from a physical constraint, retaining contradiction. -/
def classes (input : SourceEqualityPrecheck.Constraint) : Option Constraints := input.map (List.map Record.paths)

/-- Physical records and their actual class path sets have identical equality meaning. -/
theorem classes_sat (input : SourceEqualityPrecheck.Constraint) (term : Term Symbol) :
    Sat term (classes input) ↔ SourceEqualityPrecheck.Sat term input := by cases input <;> rfl

/-- Every successful normalized physical readback derives the ascending trie invariant. -/
theorem read_wellFormed (equalities : Option Constraints) (cached : Cached equalities)
    (payload : SourceEqualityPrecheck.Constraint) (done : SourceEqualityPhysicalPayload.read equalities = .ok payload) : WellFormed payload := by
  cases equalities with
  | none =>
      have same : payload = none := by simpa only [SourceEqualityPhysicalPayload.read, Except.ok.injEq] using done.symm
      subst payload
      simp [WellFormed]
  | some paths =>
      obtain ⟨records, built, valid, _⟩ := SourceEqualityPhysicalPayload.normal_records paths (cached paths rfl)
      have same : payload = some records := by simpa only [SourceEqualityPhysicalPayload.read, built, Except.ok.injEq] using done.symm
      subst payload
      intro originals equal original member
      cases equal
      exact ⟨(valid original member).1, SourceEqualityDescend.recordsOf_ascending paths records built original member, (valid original member).2⟩

/-- Actual normalized physical readback is finite and derives all inherited representation facts. -/
theorem read_complete (equalities : Option Constraints) (cached : Cached equalities) :
    ∃ payload, SourceEqualityPhysicalPayload.read equalities = .ok payload ∧ WellFormed payload ∧
      ∀ term : Term Symbol, SourceEqualityPrecheck.Sat term payload ↔ Sat term equalities := by
  obtain ⟨payload, built, _, exact⟩ := SourceEqualityPhysicalPayload.complete (Symbol := Symbol) equalities cached
  exact ⟨payload, built, read_wellFormed equalities cached payload built, exact⟩

/-- The actual source combiner uses inherited records first and local records second. -/
noncomputable def combine (inherited own : SourceEqualityPrecheck.Constraint) : Except String SourceEqualityPrecheck.Constraint :=
  SourceEqualityPhysicalPayload.read (SourceCompactGuards.combineEqualities (classes inherited) (classes own))

/-- Source combination derives finite coherent physical output and exact conjunction without an input normal-form premise. -/
theorem combine_complete (inherited own : SourceEqualityPrecheck.Constraint) :
    ∃ combined, combine inherited own = .ok combined ∧ WellFormed combined ∧
      ∀ term : Term Symbol, SourceEqualityPrecheck.Sat term combined ↔
        SourceEqualityPrecheck.Sat term inherited ∧ SourceEqualityPrecheck.Sat term own := by
  obtain ⟨combined, built, valid, exact⟩ := read_complete (Symbol := Symbol)
    (SourceCompactGuards.combineEqualities (classes inherited) (classes own)) (combine_cached _ _)
  refine ⟨combined, built, valid, ?_⟩
  intro term
  exact (exact term).trans ((SourceEqualityPCSGuard.combine_sat _ _ term).trans (and_congr (classes_sat inherited term) (classes_sat own term)))

/-- Every actual completed source combination has the same derived physical invariant and exact meaning. -/
theorem combine_exact {inherited own combined : SourceEqualityPrecheck.Constraint} (done : combine inherited own = .ok combined) :
    WellFormed combined ∧ ∀ term : Term Symbol, SourceEqualityPrecheck.Sat term combined ↔
      SourceEqualityPrecheck.Sat term inherited ∧ SourceEqualityPrecheck.Sat term own := by
  obtain ⟨actual, built, valid, exact⟩ := combine_complete (Symbol := Symbol) inherited own
  have same : actual = combined := Except.ok.inj (built.symm.trans done)
  subst actual
  exact ⟨valid, exact⟩

/-- Completed source combination has exact readback to the existing combined-constraint worker. -/
theorem combine_readback (inherited own : SourceEqualityPrecheck.Constraint) :
    combine inherited own = SourceEqualityPhysicalPayload.read (SymbolicEqualityBridge.resultClasses (SourceEqualityPrecheck.combine inherited own)) := by
  cases inherited with
  | none => rfl
  | some inherited =>
      cases own with
      | none => rfl
      | some own =>
          cases inherited <;> cases own <;>
            simp only [combine, classes, Option.map_some, List.map_nil, List.map_cons, SourceCompactGuards.combineEqualities,
              SourceCompactGuards.normalize, SourceCompactGuards.arrayNormalize_eq, SourceEqualityPrecheck.combine, SymbolicEqualityBridge.resultClasses]

/-- The bounded array adapter retains normalization timeout as an incomplete observation. -/
def combineArray (work : Nat) (inherited own : SourceEqualityPrecheck.Constraint) : Option (Except String SourceEqualityPrecheck.Constraint) :=
  match SourceEqualityPrecheck.combineArray work inherited own with
  | .timeout => none
  | .contradiction => some (.ok none)
  | .normalized output => some (SourceEqualityPhysicalPayload.read (some output))

/-- Every sufficient actual array work bound returns the identical combined physical payload, including checked errors. -/
theorem combineArray_eventual (inherited own : SourceEqualityPrecheck.Constraint) :
    ∃ bound, ∀ work, bound ≤ work → combineArray work inherited own = some (combine inherited own) := by
  obtain ⟨bound, agrees⟩ := SourceEqualityPrecheck.combineArray_eventual inherited own
  refine ⟨bound, ?_⟩
  intro work enough
  rw [combineArray, agrees work enough, combine_readback]
  cases result : SourceEqualityPrecheck.combine inherited own with
  | timeout => exact False.elim (SourceEqualityPrecheck.combine_complete inherited own result)
  | contradiction | normalized => rfl

/-- Actual full source guard readback derives an ascending physical own payload. -/
theorem own_complete [DecidableEq Formula] (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (constraint : SourceSymbolicIndex.Constraint Formula) (stored : Cached constraint.equalities) :
    ∃ own, SourceEqualityPhysicalPayload.own constraint = .ok own ∧ WellFormed own ∧
      ∀ term : Term (SourceObservations.Label Formula), SourceSymbolicIndex.acceptsConstraint formulas solver constraint term = true →
        SourceEqualityPrecheck.Sat term own := by
  obtain ⟨own, built, valid, exact⟩ := read_complete (Symbol := SourceObservations.Label Formula)
    (SourceCompactGuards.sourceEqualities constraint) (source_cached constraint stored)
  exact ⟨own, built, valid, fun term accepted => (exact term).mpr (accepted_sat formulas solver constraint (active stored) term accepted)⟩

/-- The actual inherited/local combination supplies the actual descended payload for each existing child. -/
theorem combined_child {inherited own combined : SourceEqualityPrecheck.Constraint} (done : combine inherited own = .ok combined)
    (symbol : Symbol) (children : List (Term Symbol)) (index : Nat) (child : Term Symbol) (found : children[index]? = some child)
    (inheritedSat : SourceEqualityPrecheck.Sat (.node symbol children) inherited) (ownSat : SourceEqualityPrecheck.Sat (.node symbol children) own) :
    SourceEqualityPrecheck.Sat child (SourceEqualityDescend.descend combined index) := by
  have checked := combine_exact (Symbol := Symbol) done
  exact SourceEqualityDescend.descend_sound combined checked.1 symbol children index child found ((checked.2 _).mpr ⟨inheritedSat, ownSat⟩)

end MicroCFTA.SourceEqualityInheritedPayload
