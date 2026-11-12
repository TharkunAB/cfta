import MicroCFTA.SourceSynthesisCurrentGroupAdmission
import MicroCFTA.SourceSynthesisCurrentTypeAdmission
import MicroCFTA.SourceSynthesisContextApplications

/-!
# Raw admission to current source terms

The certificate retains original binding origins, raw substitutions, roles,
and marked query tokens. Only demanded images and application results need
raw universe admission. Query leaves use the original last binding.
The proof constructs current terms membership for the same Program and body.
It does not assert relevant/root membership or native execution.
-/
namespace MicroCFTA.SourceSynthesisCurrentProgramAdmission
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax (Ty Library Query variableSymbol)
open SourceSynthesisGeneralizeSyntax (variables)
open SourceSynthesisFirstOrderConstruction (termsRows)
open SourceSynthesisCurrentContext (context constructorCatalog context_types)
open SourceSynthesisCurrentTypeAdmission (RawAdmitted typeIn_iff_admitted)
open SourceSynthesisPr210TypeReflection (encodeTy candidateRigid candidateRigid_eq_iff)
open SourceSynthesisTypeSubstitutionWitnesses (substTy)
open SourceSynthesisOrdinaryTyping (Typed Equivalent queryLookup)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

/-- Record original choices and demanded admission without source-success fields. -/
inductive Eligible (lib : Library) (query : Query) :
    Bool → Program → Ty → List (String × Ty) → Prop where
  | group (asArgument : Bool) (entry : String × Ty × List String)
      (binding : entry ∈ lib.libraryGroups) (rho : String → Ty)
      (images : ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2.1) →
        RawAdmitted (constructorCatalog lib query) (rho raw)) :
      Eligible lib query asArgument (.var entry.1) (substTy rho entry.2.1) []
  | argumentOnly (entry : String × Ty) (binding : entry ∈ lib.libraryArgumentOnly)
      (rho : String → Ty)
      (images : ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2) →
        RawAdmitted (constructorCatalog lib query) (rho raw)) :
      Eligible lib query true (.var entry.1) (substTy rho entry.2) []
  | queryArgument (asArgument : Bool) (name : String) (typ : Ty)
      (found : queryLookup query.queryArguments name = some typ) :
      Eligible lib query asArgument (.var name) typ []
  | queryToken (asArgument : Bool) (token : String × Ty) (typ : Ty)
      (found : queryLookup query.queryArguments token.1 = some typ) :
      Eligible lib query asArgument (.var token.1) typ [token]
  | application {asArgument : Bool} {function argument : Program} {domain codomain : Ty}
      {left right : List (String × Ty)}
      (first : Eligible lib query false function (.tFun domain codomain) left)
      (second : Eligible lib query true argument domain right)
      (result : RawAdmitted (constructorCatalog lib query) codomain) :
      Eligible lib query asArgument (.app function argument) codomain (left ++ right)
  | conversion {asArgument : Bool} {program : Program} {first second : Ty}
      {tokens : List (String × Ty)}
      (admitted : Eligible lib query asArgument program first tokens)
      (same : Equivalent first second) :
      Eligible lib query asArgument program second tokens

private theorem components_pos (program : Program) : 0 < program.components := by
  induction program with
  | var _ => exact Nat.zero_lt_succ 0
  | app function argument first second =>
      change 0 < function.components + argument.components
      omega

/-- Raw current admission constructs ordinary typing and the same actual terms witness. -/
theorem eligible_program_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool} {program : Program} {typ : Ty}
    {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : Eligible lib query asArgument program typ tokens) :
    Typed lib query program typ ∧
      ∃ body expression, expression ∈ termsRows (context lib query) asArgument program.components ∧
        evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) body ∧
          body.atPath [0] = some (candidateRigid typ) ∧
          Projection literal Prod.fst body program ∧
          toProgram literal Prod.fst body = program ∧
          (toProgram literal Prod.fst body).components = program.components := by
  induction eligible with
  | group asArgument entry binding rho images =>
      obtain ⟨ordinary, expression, member, accepted, annotation, projected, decoded, counted⟩ :=
        SourceSynthesisCurrentGroupAdmission.group_member formulas solver lib query asArgument
          entry binding rho (fun raw needed =>
            (typeIn_iff_admitted lib query (rho raw)).mpr (images raw needed))
      exact ⟨ordinary, .node (literal entry.1) [candidateRigid (substTy rho entry.2.1)],
        expression, member, accepted, annotation, projected, decoded, counted⟩
  | argumentOnly entry binding rho images =>
      obtain ⟨ordinary, expression, member, accepted, annotation, projected, decoded, counted⟩ :=
        SourceSynthesisCurrentGroupAdmission.argumentOnly_member formulas solver lib query true
          entry binding rho rfl (fun raw needed =>
            (typeIn_iff_admitted lib query (rho raw)).mpr (images raw needed))
      exact ⟨ordinary, .node (literal entry.1) [candidateRigid (substTy rho entry.2)],
        expression, member, accepted, annotation, projected, decoded, counted⟩
  | queryArgument asArgument name typ found =>
      obtain ⟨ordinary, expression, member, accepted, annotation, projected, decoded, counted⟩ :=
        SourceSynthesisCurrentContext.query_argument_member formulas solver lib query asArgument name typ found
      exact ⟨ordinary, .node (literal name) [candidateRigid typ], expression,
        member, accepted, annotation, projected, decoded, counted⟩
  | queryToken asArgument token typ found =>
      obtain ⟨ordinary, expression, member, accepted, annotation, projected, decoded, counted⟩ :=
        SourceSynthesisCurrentContext.query_argument_member formulas solver lib query asArgument token.1 typ found
      exact ⟨ordinary, .node (literal token.1) [candidateRigid typ], expression,
        member, accepted, annotation, projected, decoded, counted⟩
  | @application asArgument function argument domain codomain _left _right _first _second result firstIH secondIH =>
      obtain ⟨functionOrdinary, functionBody, functionExpression, functionMember, functionAccepted,
          functionAnnotation, functionProjected, _functionDecoded, _functionCount⟩ := firstIH
      obtain ⟨argumentOrdinary, argumentBody, argumentExpression, argumentMember, argumentAccepted,
          argumentAnnotation, argumentProjected, _argumentDecoded, _argumentCount⟩ := secondIH
      have functionType : functionBody.atPath [0] =
          some (.node (literal "->") [marker, candidateRigid domain, candidateRigid codomain]) := by
        simpa only [candidateRigid, encodeTy, SourceSynthesisFiniteTypeWitnesses.rigidTerm] using functionAnnotation
      obtain ⟨expression, member, accepted⟩ :=
        SourceSynthesisContextApplications.terms_application_member_at formulas solver
          (context lib query) (constructorCatalog lib query) (context_types lib query) unpruned
          asArgument function.components argument.components (components_pos function) (components_pos argument)
          (candidateRigid domain) (candidateRigid codomain) functionBody argumentBody
          ⟨functionExpression, functionMember, functionAccepted⟩
          ⟨argumentExpression, argumentMember, argumentAccepted⟩ functionType argumentAnnotation
          ((typeIn_iff_admitted lib query codomain).mpr result)
      let body : Term Symbol :=
        .node (literal "app") [candidateRigid codomain, marker, functionBody, argumentBody]
      have projected : Projection literal Prod.fst body (.app function argument) :=
        .application _ _ functionProjected argumentProjected
      have decoded := projected.toProgram_eq
      exact ⟨.application functionOrdinary argumentOrdinary, body, expression,
        member, accepted, rfl, projected, decoded, congrArg Program.components decoded⟩
  | @conversion _asArgument _program first second _tokens _admitted same ih =>
      obtain ⟨ordinary, body, expression, member, accepted, annotation, projected, decoded, counted⟩ := ih
      have encoded := (candidateRigid_eq_iff first second).mpr same
      exact ⟨.conversion ordinary same, body, expression, member, accepted,
        annotation.trans (congrArg some encoded), projected, decoded, counted⟩

end MicroCFTA.SourceSynthesisCurrentProgramAdmission
