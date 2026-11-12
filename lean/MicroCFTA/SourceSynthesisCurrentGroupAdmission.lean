import MicroCFTA.SourceSynthesisCurrentContext
import MicroCFTA.SourceSynthesisPr210Substitution

/-!
# Current component-leaf admission

Original bindings and raw per-use substitutions determine each accepted leaf.
Constructor escaping supplies alias safety. Only demanded variable images
require current universe admission. The current Context and row evaluator
remain unchanged. These laws do not assert whole Program or root acceptance.
-/
namespace MicroCFTA.SourceSynthesisCurrentGroupAdmission
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax (Ty Library Query allTypes variableSymbol)
open SourceSynthesisGeneralizeSyntax (Guard top variables)
open SourceSynthesisFirstOrderConstruction (Row component termsRows)
open SourceSynthesisCurrentContext (context constructorCatalog)
open SourceSynthesisPr210TypeReflection (encodeTy candidateRigid)
open SourceSynthesisPr210Substitution (encodeTy_aliasSafe substTy_encodeTy)
open SourceSynthesisTypeSubstitutionWitnesses (substTy)
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourceSynthesisSourceTermsTyping (LeafTyping)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapEdges mapEdges_eq_map)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private theorem instance_leaf (catalog : List (String × Nat)) (name : String)
    (scheme : Ty) (rho : String → Ty)
    (admitted : ∀ raw, variableSymbol raw ∈ variables (encodeTy scheme) →
      TypeIn catalog (candidateRigid (rho raw))) :
    LeafTyping catalog (component (allTypes top catalog) name (encodeTy scheme)) (.var name)
      (candidateRigid (substTy rho scheme))
      (.node (literal name) [candidateRigid (substTy rho scheme)]) := by
  have typed := SourceSynthesisEncodedSubstitutionLift.component_instance_leaf catalog name
    (encodeTy scheme) (fun raw => encodeTy (rho raw)) (encodeTy_aliasSafe scheme) admitted
  simpa only [candidateRigid, substTy_encodeTy] using typed

private theorem leaf_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {catalog : List (String × Nat)} {row : Row} {program : Program}
    {annotation term : Term Symbol} (typed : LeafTyping catalog row program annotation term) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.node [row])) term := by
  cases typed with
  | component name typ substitution images =>
      exact SourceSynthesisAnnotatedProgramWitnesses.component_member formulas solver catalog
        name typ substitution images
  | argument name typ =>
      exact SourceSynthesisAnnotatedProgramWitnesses.argument_member formulas solver name typ

private theorem node_member (holds : Guard → Term Symbol → Bool) (rows : List Row) (row : Row)
    (term : Term Symbol) (selected : row ∈ rows)
    (accepted : evaluate holds [] (mapSyntax literal (.node [row])) term) :
    evaluate holds [] (mapSyntax literal (.node rows)) term := by
  have included : ∀ mapped ∈ mapEdges literal [row], mapped ∈ mapEdges literal rows := by
    rw [mapEdges_eq_map, mapEdges_eq_map]
    intro mapped present
    obtain ⟨source, member, rfl⟩ := List.mem_map.mp present
    have same := List.mem_singleton.mp member
    subst source
    exact List.mem_map.mpr ⟨row, selected, rfl⟩
  rw [mapSyntax, evaluate] at accepted ⊢
  obtain ⟨⟨mapped, member⟩, accepted⟩ := accepted
  exact ⟨⟨mapped, included mapped member⟩, accepted⟩

/-- A selected group instance belongs to the actual current size-one source pool. -/
theorem group_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool)
    (entry : String × Ty × List String) (binding : entry ∈ lib.libraryGroups)
    (rho : String → Ty)
    (admitted : ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2.1) →
      TypeIn (constructorCatalog lib query) (candidateRigid (rho raw))) :
    let typ := substTy rho entry.2.1
    let term : Term Symbol := .node (literal entry.1) [candidateRigid typ]
    Typed lib query (.var entry.1) typ ∧
      ∃ expression ∈ termsRows (context lib query) asArgument 1,
        evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) term ∧
          term.atPath [0] = some (candidateRigid typ) ∧
          Projection literal Prod.fst term (.var entry.1) ∧
          toProgram literal Prod.fst term = .var entry.1 ∧
          (toProgram literal Prod.fst term).components = 1 := by
  have typed := instance_leaf (constructorCatalog lib query) entry.1 entry.2.1 rho admitted
  let row : Row := component (context lib query).types entry.1 (encodeTy entry.2.1)
  have selected : row ∈ (context lib query).components.map Prod.snd := by
    change row ∈ (lib.libraryGroups.map fun source =>
      (source.1, component (context lib query).types source.1 (encodeTy source.2.1))).map Prod.snd
    rw [List.map_map]
    exact List.mem_map.mpr ⟨entry, binding, rfl⟩
  have projected := typed.shape.2.1
  have decoded := projected.toProgram_eq
  refine ⟨.group entry binding rho, .node ((context lib query).components.map Prod.snd), ?_,
    node_member (SourceEqualityPCSGuard.holds formulas solver) _ row _ selected
      (leaf_member formulas solver typed), typed.shape.1, projected, decoded, ?_⟩
  · rw [SourceSynthesisFirstOrderConstruction.termsRows_one]
    exact List.mem_append.mpr (.inl (by simp))
  · exact congrArg Program.components decoded

/-- An argument-only instance belongs to its actual current argument-position pool. -/
theorem argumentOnly_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool)
    (entry : String × Ty) (binding : entry ∈ lib.libraryArgumentOnly)
    (rho : String → Ty) (role : asArgument = true)
    (admitted : ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2) →
      TypeIn (constructorCatalog lib query) (candidateRigid (rho raw))) :
    let typ := substTy rho entry.2
    let term : Term Symbol := .node (literal entry.1) [candidateRigid typ]
    Typed lib query (.var entry.1) typ ∧
      ∃ expression ∈ termsRows (context lib query) asArgument 1,
        evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) term ∧
          term.atPath [0] = some (candidateRigid typ) ∧
          Projection literal Prod.fst term (.var entry.1) ∧
          toProgram literal Prod.fst term = .var entry.1 ∧
          (toProgram literal Prod.fst term).components = 1 := by
  subst asArgument
  have typed := instance_leaf (constructorCatalog lib query) entry.1 entry.2 rho admitted
  let row : Row := component (context lib query).types entry.1 (encodeTy entry.2)
  let rows : List Row := lib.libraryArgumentOnly.map fun source =>
    component (context lib query).types source.1 (encodeTy source.2)
  have selected : row ∈ rows := List.mem_map.mpr ⟨entry, binding, rfl⟩
  have projected := typed.shape.2.1
  have decoded := projected.toProgram_eq
  refine ⟨.argumentOnly entry binding rho, (context lib query).argumentOnly, ?_,
    node_member (SourceEqualityPCSGuard.holds formulas solver) rows row _ selected
      (leaf_member formulas solver typed), typed.shape.1, projected, decoded, ?_⟩
  · rw [SourceSynthesisFirstOrderConstruction.termsRows_one]
    exact List.mem_append.mpr (.inr (by simp))
  · exact congrArg Program.components decoded

end MicroCFTA.SourceSynthesisCurrentGroupAdmission
