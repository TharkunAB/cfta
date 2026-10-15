import MicroCFTA.SourceEqualityGuardedEdgeEffects

/-!
# Independent language of the actual reconstructed guarded edge

Complete guard acceptance derives own class satisfaction from the actual
source accessor. The original full guard is retained. Inherited equality
satisfaction remains the surrounding context of an exact edge pass.
-/
namespace MicroCFTA.SourceEqualityGuardedEdgeLanguage
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
    (clearTrue : ∀ guard, clear guard = true → ∀ term, acceptsConstraint formulas solver guard term = true)
    (topTrue : ∀ term, acceptsConstraint formulas solver top term = true)
    (conjoined : ∀ first second term, acceptsConstraint formulas solver (conjoin first second) term =
      (acceptsConstraint formulas solver first term && acceptsConstraint formulas solver second term))
    (term : Term Symbol) :
    (edgeMeaning (acceptsConstraint formulas solver) ambient result term → edgeMeaning (acceptsConstraint formulas solver) ambient edge term) ∧
      (SourceEqualityPrecheck.Sat term inherited →
        (edgeMeaning (acceptsConstraint formulas solver) ambient result term ↔ edgeMeaning (acceptsConstraint formulas solver) ambient edge term)) := by
  cases trace with
  | @done payload results middle physical pass =>
      obtain ⟨ownPayload, actual, valid, _, acceptedOwn⟩ := SourceEqualityPhysicalPayload.own_complete formulas solver edge.entry.key.constraint stored
      have same := Except.ok.inj (actual.symm.trans physical)
      subst ownPayload
      have effects := SourceEqualityOnePassEffects.effects pass ready available closed
      have fields := MergedPhysicalGroupEdges.makeEdge_fields _ effects.1.semantic.ready.semantic.1.normal.facts
        edge.entry.key.symbol edge.entry.key.constraint _ effects.2.2.1
      rw [InternedGuardedLanguage.edgeMeaning_all, InternedGuardedLanguage.edgeMeaning_all]
      simp only [MergedColdInterpretation.EdgeMeaning, fields.1, fields.2.1, fields.2.2]
      have narrows : (∃ terms, term = .node edge.entry.key.symbol terms ∧ All₂ (meaning (acceptsConstraint formulas solver) ambient) results terms ∧
          acceptsConstraint formulas solver edge.entry.key.constraint term = true) →
          ∃ terms, term = .node edge.entry.key.symbol terms ∧ All₂ (meaning (acceptsConstraint formulas solver) ambient) edge.children terms ∧
            acceptsConstraint formulas solver edge.entry.key.constraint term = true := by
        rintro ⟨terms, shape, runs, guard⟩
        have bounds := SourceEqualityOnePassLanguage.language pass valid ready available closed
          (acceptsConstraint formulas solver) ambient clearTrue topTrue conjoined edge.entry.key.symbol terms
        exact ⟨terms, shape, bounds.1 runs, guard⟩
      refine ⟨narrows, fun inheritedSat => ⟨narrows, ?_⟩⟩
      rintro ⟨terms, shape, runs, guard⟩
      have bounds := SourceEqualityOnePassLanguage.language pass valid ready available closed
        (acceptsConstraint formulas solver) ambient clearTrue topTrue conjoined edge.entry.key.symbol terms
      exact ⟨terms, shape, bounds.2 (shape ▸ acceptedOwn term guard) (shape ▸ inheritedSat) runs, guard⟩

end MicroCFTA.SourceEqualityGuardedEdgeLanguage
