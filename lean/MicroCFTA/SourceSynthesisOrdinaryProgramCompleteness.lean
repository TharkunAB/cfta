import MicroCFTA.SourceSynthesisOrdinaryLeafCompleteness

/-!
# Admitted ordinary Programs in unpruned source terms

The external certificate retains each leaf's selected raw instance and role.
Application sends false to the function and true to the argument. Only its
result annotation requires a new TypeIn premise. Ordinary typing remains
independent of these admission facts.

An empty avoid list permits the actual size-two fallback row. Larger Programs
use the source's positive splits. These laws concern Nat-indexed terms cells.
Relevant/root admission, public API completeness, machine Int conversion, and
unrestricted encoded reflection remain separate.
-/
namespace MicroCFTA.SourceSynthesisOrdinaryProgramCompleteness
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax
open SourceSynthesisFirstOrderConstruction (constructorCatalog context termsRows)
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed Equivalent equivalent_rigidTerm)
open SourceSynthesisOrdinaryLeafCompleteness (LeafEligible eligible_leaf_terms)
open SourceSynthesisSourceTermsTyping (LeafTyping TermsTyping oneRows withoutRows fallbackFunctionRows)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

/-- Record an admitted ordinary derivation with the actual source argument roles. -/
inductive ProgramEligible (lib : Library) (query : Query) : Bool → Program → Ty → Prop where
  | leaf {asArgument : Bool} {name : String} {typ : Ty}
      (eligible : LeafEligible lib query asArgument (.var name) typ) :
      ProgramEligible lib query asArgument (.var name) typ
  | application {asArgument : Bool} {function argument : Program} {domain codomain : Ty}
      (first : ProgramEligible lib query false function (.tFun domain codomain))
      (second : ProgramEligible lib query true argument domain)
      (result : TypeIn (constructorCatalog lib query) (rigidTerm codomain)) :
      ProgramEligible lib query asArgument (.app function argument) codomain
  | conversion {asArgument : Bool} {program : Program} {first second : Ty}
      (eligible : ProgramEligible lib query asArgument program first)
      (same : Equivalent first second) :
      ProgramEligible lib query asArgument program second

private theorem components_pos (program : Program) : 0 < program.components := by
  induction program with
  | var _name => exact Nat.zero_lt_succ 0
  | app function argument first second =>
      change 0 < function.components + argument.components
      omega

private theorem unpruned_function_leaf {lib : Library} {query : Query}
    {program : Program} {annotation term : Term Symbol}
    (unpruned : lib.libraryAvoid = [])
    (typed : TermsTyping lib query false 1 program annotation term) :
    ∃ row, row ∈ fallbackFunctionRows (context lib query) ∧
      LeafTyping (constructorCatalog lib query) row program annotation term := by
  cases typed with
  | leaf selected leaf =>
      refine ⟨_, ?_, leaf⟩
      have cleared : (context lib query).avoid = [] := unpruned
      simpa [oneRows, fallbackFunctionRows, withoutRows, cleared, or_comm] using selected
  | split large _positive _smaller _function _argument _result => omega

/-- An admitted Program has ordinary typing and an exact source receipt at its component count. -/
theorem eligible_program_terms {lib : Library} {query : Query}
    {asArgument : Bool} {program : Program} {typ : Ty}
    (unpruned : lib.libraryAvoid = [])
    (eligible : ProgramEligible lib query asArgument program typ) :
    Typed lib query program typ ∧
      ∃ term, TermsTyping lib query asArgument program.components program (rigidTerm typ) term := by
  induction eligible with
  | @leaf asArgument name typ eligible =>
      obtain ⟨ordinary, source⟩ := eligible_leaf_terms eligible
      exact ⟨ordinary, _, source⟩
  | @application asArgument function argument domain codomain first second result firstIH secondIH =>
      obtain ⟨functionOrdinary, functionTerm, functionSource⟩ := firstIH
      obtain ⟨argumentOrdinary, argumentTerm, argumentSource⟩ := secondIH
      simp only [rigidTerm] at functionSource
      let term : Term Symbol :=
        .node (literal "app") [rigidTerm codomain, marker, functionTerm, argumentTerm]
      refine ⟨.application functionOrdinary argumentOrdinary, term, ?_⟩
      have functionPositive := components_pos function
      have argumentPositive := components_pos argument
      by_cases two : function.components + argument.components = 2
      · have functionOne : function.components = 1 := by omega
        have argumentOne : argument.components = 1 := by omega
        rw [functionOne] at functionSource
        rw [argumentOne] at argumentSource
        obtain ⟨row, selected, leaf⟩ := unpruned_function_leaf unpruned functionSource
        have constructed : TermsTyping lib query asArgument 2 (.app function argument)
            (rigidTerm codomain) term :=
          .fallback selected leaf argumentSource result
        simpa only [Program.components, two] using constructed
      · have large : 3 ≤ function.components + argument.components := by omega
        have smaller : function.components < function.components + argument.components := by omega
        have remaining : function.components + argument.components - function.components =
            argument.components := by omega
        have argumentSplit : TermsTyping lib query true
            (function.components + argument.components - function.components) argument
            (rigidTerm domain) argumentTerm := by
          simpa only [remaining] using argumentSource
        have constructed : TermsTyping lib query asArgument
            (function.components + argument.components) (.app function argument)
            (rigidTerm codomain) term :=
          .split large functionPositive smaller functionSource argumentSplit result
        exact constructed
  | @conversion asArgument program first second eligible same ih =>
      obtain ⟨ordinary, term, source⟩ := ih
      refine ⟨.conversion ordinary same, term, ?_⟩
      have encoded := equivalent_rigidTerm first second same
      simpa only [encoded] using source

/-- Membership, annotation, decoding, and component count refer to the same ordinary Program term. -/
theorem eligible_program_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool} {program : Program} {typ : Ty}
    (unpruned : lib.libraryAvoid = [])
    (eligible : ProgramEligible lib query asArgument program typ) :
    Typed lib query program typ ∧
      ∃ term, ∃ expression ∈ termsRows (context lib query) asArgument program.components,
        evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) term ∧
          term.atPath [0] = some (rigidTerm typ) ∧
          Projection literal Prod.fst term program ∧
          toProgram literal Prod.fst term = program ∧
          (toProgram literal Prod.fst term).components = program.components := by
  obtain ⟨ordinary, term, source⟩ := eligible_program_terms unpruned eligible
  obtain ⟨expression, member, accepted⟩ := TermsTyping.member formulas solver source
  obtain ⟨annotation, projected, _count⟩ := TermsTyping.shape source
  have decoded := projected.toProgram_eq
  exact ⟨ordinary, term, expression, member, accepted, annotation, projected, decoded,
    congrArg Program.components decoded⟩

end MicroCFTA.SourceSynthesisOrdinaryProgramCompleteness
