import MicroCFTA.SourceSynthesisOrdinaryTyping
import MicroCFTA.SourceSynthesisEncodedSubstitutionLift

/-!
# Ordinary leaf admission to actual source terms

The external certificate records an admitted ordinary leaf derivation.
Each component occurrence supplies its own raw substitution. Only demanded
images require TypeIn. Original schemes retain AliasSafe. Argument-only
bindings require the argument role. Query types remain rigid.

The certificate has no application case. It contains no source typing,
membership, successful output, or encoded substitution premise. The laws
construct ordinary typing and membership for the same literal typed term.
Relevant/root admission and unrestricted encoded reflection remain separate.
-/
namespace MicroCFTA.SourceSynthesisOrdinaryLeafCompleteness
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (variables)
open SourceSynthesisFirstOrderConstruction (constructorCatalog context termsRows)
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed Equivalent queryLookup queryLookup_member equivalent_rigidTerm)
open SourceSynthesisTypeSubstitutionWitnesses (substTy AliasSafe)
open SourceSynthesisSourceTermsTyping (TermsTyping)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- Admit one ordinary leaf derivation from its selected raw binding and images. -/
inductive LeafEligible (lib : Library) (query : Query) (asArgument : Bool) :
    Program → Ty → Prop where
  | group (entry : String × Ty × List String) (binding : entry ∈ lib.libraryGroups)
      (rho : String → Ty) (safe : AliasSafe entry.2.1)
      (admitted : ∀ raw, variableSymbol raw ∈ variables entry.2.1 →
        TypeIn (constructorCatalog lib query) (rigidTerm (rho raw))) :
      LeafEligible lib query asArgument (.var entry.1) (substTy rho entry.2.1)
  | argumentOnly (entry : String × Ty) (binding : entry ∈ lib.libraryArgumentOnly)
      (rho : String → Ty) (role : asArgument = true) (safe : AliasSafe entry.2)
      (admitted : ∀ raw, variableSymbol raw ∈ variables entry.2 →
        TypeIn (constructorCatalog lib query) (rigidTerm (rho raw))) :
      LeafEligible lib query asArgument (.var entry.1) (substTy rho entry.2)
  | queryArgument {name : String} {typ : Ty}
      (found : queryLookup query.queryArguments name = some typ) :
      LeafEligible lib query asArgument (.var name) typ
  | conversion {program : Program} {first second : Ty}
      (eligible : LeafEligible lib query asArgument program first)
      (same : Equivalent first second) :
      LeafEligible lib query asArgument program second

private theorem eligible_derivation {lib : Library} {query : Query} {asArgument : Bool}
    {program : Program} {typ : Ty} (eligible : LeafEligible lib query asArgument program typ) :
    ∃ name, program = .var name ∧ Typed lib query program typ ∧
      TermsTyping lib query asArgument 1 program (rigidTerm typ)
        (.node (literal name) [rigidTerm typ]) := by
  induction eligible with
  | group entry binding rho safe admitted =>
      exact ⟨entry.1, rfl, .group entry binding rho,
        SourceSynthesisEncodedSubstitutionLift.group_instance_terms
          lib query asArgument entry binding rho safe admitted⟩
  | argumentOnly entry binding rho role safe admitted =>
      cases role
      exact ⟨entry.1, rfl, .argumentOnly entry binding rho,
        SourceSynthesisEncodedSubstitutionLift.argumentOnly_instance_terms
          lib query entry binding rho safe admitted⟩
  | @queryArgument name typ found =>
      exact ⟨name, rfl, .queryArgument found,
        SourceSynthesisTypeSubstitutionWitnesses.query_argument_terms lib query asArgument
          (name, typ) (queryLookup_member query.queryArguments name typ found)⟩
  | @conversion program first second eligible same ih =>
      obtain ⟨name, shape, ordinary, source⟩ := ih
      refine ⟨name, shape, .conversion ordinary same, ?_⟩
      have encoded := equivalent_rigidTerm first second same
      simpa only [encoded] using source

/-- The admitted leaf has ordinary typing and the exact literal size-one source derivation. -/
theorem eligible_leaf_terms {lib : Library} {query : Query} {asArgument : Bool}
    {name : String} {typ : Ty} (eligible : LeafEligible lib query asArgument (.var name) typ) :
    Typed lib query (.var name) typ ∧
      TermsTyping lib query asArgument 1 (.var name) (rigidTerm typ)
        (.node (literal name) [rigidTerm typ]) := by
  obtain ⟨selected, shape, ordinary, source⟩ := eligible_derivation eligible
  have names := Program.var.inj shape
  subst selected
  exact ⟨ordinary, source⟩

/-- Actual terms membership, annotation, projection, and decoding refer to the same typed leaf. -/
theorem eligible_leaf_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool} {name : String} {typ : Ty}
    (eligible : LeafEligible lib query asArgument (.var name) typ) :
    let term : Term Symbol := .node (literal name) [rigidTerm typ]
    Typed lib query (.var name) typ ∧
      ∃ expression ∈ termsRows (context lib query) asArgument 1,
        evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) term ∧
          term.atPath [0] = some (rigidTerm typ) ∧
          Projection literal Prod.fst term (.var name) ∧
          toProgram literal Prod.fst term = .var name := by
  obtain ⟨ordinary, source⟩ := eligible_leaf_terms eligible
  obtain ⟨expression, member, accepted⟩ := TermsTyping.member formulas solver source
  obtain ⟨annotation, projected, _count⟩ := TermsTyping.shape source
  exact ⟨ordinary, expression, member, accepted, annotation, projected, projected.toProgram_eq⟩

end MicroCFTA.SourceSynthesisOrdinaryLeafCompleteness
