import MicroCFTA.SourceEqualityGuardedEdgeEffects
import MicroCFTA.SourceEqualityPCSConstructors
import MicroCFTA.GuardStructuralOrder

/-!
# Independent PCS language of actual guarded-edge reconstruction

Independent complete guard acceptance derives own class satisfaction from
the actual source accessor. Concrete source constructors have global laws
at this PCS meaning. Normalized annotations retain exact public readback.
-/
namespace MicroCFTA.SourceEqualityPCSGuardedEdge
open Language InternedConstructorTemplates InternedNestedProvenance
open SourceEqualityNativeScoped SourceEqualityClassFoldGraph SourceEqualityGuardedEdgeGraph
open SourceObservations SourceGuards SourceSymbolicIndex
open InternedGuardedLanguage (meaning edgeMeaning)
open MergedColdReaderClosedInputs (ClosedValues)
variable {Formula : Type}
local notation "Symbol" => Label Formula
local notation "Guard" => Constraint Formula

/-- Actual guarded-edge processing narrows unconditionally and is exact in every satisfying inherited context. -/
theorem language [DecidableEq Formula] [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {edge result : EdgeValue Symbol Guard} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (trace : Graph unconstrained emptyGuard conjoin clear top edge inherited before result after)
    (stored : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap edge.children) (closed : ClosedValues edge.children)
    (formulas : Formulas Formula) (solver : Entailment Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, SourceEqualityPCSGuard.holds formulas solver guard term = true)
    (topTrue : ∀ term, SourceEqualityPCSGuard.holds formulas solver top term = true)
    (conjoined : ∀ first second term, SourceEqualityPCSGuard.holds formulas solver (conjoin first second) term =
      (SourceEqualityPCSGuard.holds formulas solver first term && SourceEqualityPCSGuard.holds formulas solver second term))
    (term : Term Symbol) :
    (edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term → edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term) ∧
      (SourceEqualityPrecheck.Sat term inherited →
        (edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔ edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)) := by
  cases trace with
  | @done payload results middle physical pass =>
      obtain ⟨ownPayload, actual, valid, payloadExact⟩ := @SourceEqualityPhysicalPayload.complete Symbol
        (SourceCompactGuards.sourceEqualities edge.entry.key.constraint) (SourceEqualityGuardReadback.source_cached edge.entry.key.constraint stored)
      have same := Except.ok.inj (actual.symm.trans physical)
      subst ownPayload
      have acceptedOwn (term : Term Symbol) (accepted : SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint term = true) :=
        (payloadExact term).mpr (SourceEqualityPCSGuard.own_sat formulas solver edge.entry.key.constraint term accepted)
      have effects := SourceEqualityOnePassEffects.effects pass ready available closed
      have fields := MergedPhysicalGroupEdges.makeEdge_fields _ effects.1.semantic.ready.semantic.1.normal.facts
        edge.entry.key.symbol edge.entry.key.constraint _ effects.2.2.1
      rw [InternedGuardedLanguage.edgeMeaning_all, InternedGuardedLanguage.edgeMeaning_all]
      simp only [MergedColdInterpretation.EdgeMeaning, fields.1, fields.2.1, fields.2.2]
      have narrows : (∃ terms, term = .node edge.entry.key.symbol terms ∧ All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ∧
          SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint term = true) →
          ∃ terms, term = .node edge.entry.key.symbol terms ∧ All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) edge.children terms ∧
            SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint term = true := by
        rintro ⟨terms, shape, runs, guard⟩
        have bounds := SourceEqualityOnePassLanguage.language pass valid ready available closed
          (SourceEqualityPCSGuard.holds formulas solver) ambient clearTrue topTrue conjoined edge.entry.key.symbol terms
        exact ⟨terms, shape, bounds.1 runs, guard⟩
      refine ⟨narrows, fun inheritedSat => ⟨narrows, ?_⟩⟩
      rintro ⟨terms, shape, runs, guard⟩
      have bounds := SourceEqualityOnePassLanguage.language pass valid ready available closed
        (SourceEqualityPCSGuard.holds formulas solver) ambient clearTrue topTrue conjoined edge.entry.key.symbol terms
      exact ⟨terms, shape, bounds.2 (shape ▸ acceptedOwn term guard) (shape ▸ inheritedSat) runs, guard⟩

end MicroCFTA.SourceEqualityPCSGuardedEdge
