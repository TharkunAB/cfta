import MicroCFTA.SourceSynthesisCurrentLeafTyping
import MicroCFTA.SourceSynthesisCurrentProgramAdmission

/-!
# Admission of actual current source leaves

The checked leaf receipt supplies the original binding and its role.
Group occurrences retain their own substitution and demanded image admission.
Query occurrences retain the original last lookup without universe admission.
The same term retains its annotation, projection, decoder and component count.
These unmarked leaves do not establish relevant or root coverage.
-/
namespace MicroCFTA.SourceSynthesisCurrentLeafEligibility
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression termsRows)
open SourceSynthesisCurrentContext (context)
open SourceSynthesisCurrentProgramAdmission (Eligible)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
open SourceSynthesisProgramTermSize (Projection toProgram)
open SourceSynthesisPr210TypeReflection (candidateRigid)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- Actual size-one acceptance derives raw admission at the same source role. -/
theorem size_one_eligible [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool}
    {expression : Expression} {term : Term Symbol}
    (member : expression ∈ termsRows (context lib query) asArgument 1)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ name typ,
      Eligible lib query asArgument (.var name) typ [] ∧
      term = .node (literal name) [candidateRigid typ] ∧
      term.atPath [0] = some (candidateRigid typ) ∧
      Projection literal Prod.fst term (.var name) ∧
      toProgram literal Prod.fst term = .var name ∧
      (toProgram literal Prod.fst term).components = 1 := by
  obtain ⟨name, typ, shape, _ordinary, path, projected, decoded, counted, origin⟩ :=
    SourceSynthesisCurrentLeafTyping.size_one_typed formulas solver member accepted
  have eligible : Eligible lib query asArgument (.var name) typ [] := by
    rcases origin with group | argumentOnly | queryArgument
    · obtain ⟨entry, binding, rho, rfl, rfl, images⟩ := group
      exact .group asArgument entry binding rho images
    · obtain ⟨rfl, entry, binding, rho, rfl, rfl, images⟩ := argumentOnly
      exact .argumentOnly entry binding rho images
    · obtain ⟨_binding, found⟩ := queryArgument
      exact .queryArgument asArgument name typ found
  exact ⟨name, typ, eligible, shape, path, projected, decoded, counted⟩

end MicroCFTA.SourceSynthesisCurrentLeafEligibility
