import MicroCFTA.SourceSynthesisCurrentGeneralizeReification
import MicroCFTA.SourceSynthesisCurrentRigidTypeReification

/-!
# Ordinary typing of actual current source leaves

Actual size-one row membership supplies each original binding.
The same accepted annotation supplies its raw instance or rigid query type.
The result retains the exact singleton term and its source origin.
Avoid rules and duplicate names need no extra restriction.
-/
namespace MicroCFTA.SourceSynthesisCurrentLeafTyping
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax (Ty Library Query variableSymbol)
open SourceSynthesisGeneralizeSyntax (Guard top variables generalize)
open SourceSynthesisFirstOrderConstruction (Expression Row component termsRows)
open SourceSynthesisCurrentContext (context constructorCatalog typeNode)
open SourceSynthesisPr210TypeReflection (encodeTy candidateRigid)
open SourceSynthesisPr211QueryBindings (queryBindings queryBindings_member)
open SourceSynthesisTypeSubstitutionWitnesses (substTy)
open SourceSynthesisCurrentTypeAdmission (RawAdmitted)
open SourceSynthesisOrdinaryTyping (Typed queryLookup)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges mapEdge mapEdges_eq_map)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private theorem selected_row (holds : Guard → Term Symbol → Bool)
    (rows : List Row) (term : Term Symbol)
    (accepted : evaluate holds [] (mapSyntax literal (.node rows)) term) :
    ∃ row ∈ rows, evaluate holds [] (mapSyntax literal (.node [row])) term := by
  rw [mapSyntax, evaluate] at accepted
  obtain ⟨⟨mapped, included⟩, checked⟩ := accepted
  rw [mapEdges_eq_map] at included
  obtain ⟨row, member, rfl⟩ := List.mem_map.mp included
  refine ⟨row, member, ?_⟩
  rw [mapSyntax, evaluate]
  exact ⟨⟨mapEdge literal row, by
    simp only [mapEdges_eq_map, List.map_cons, List.map_nil, List.mem_singleton]⟩, checked⟩

private theorem singleton_child (holds : Guard → Term Symbol → Bool)
    (name : String) (child : Expression) (term : Term Symbol)
    (accepted : evaluate holds [] (mapSyntax literal (.node [.mk name top [child]])) term) :
    ∃ annotation, term = .node (literal name) [annotation] ∧
      evaluate holds [] (mapSyntax literal child) annotation := by
  simp only [mapSyntax, mapEdges] at accepted
  rw [evaluate] at accepted
  obtain ⟨⟨edge, included⟩, checked⟩ := accepted
  have same := List.mem_singleton.mp included
  subst edge
  rw [edgeMeaning] at checked
  obtain ⟨terms, shape, children, _held⟩ := checked
  cases terms with
  | nil => simp only [mapChildren, forest] at children
  | cons annotation rest =>
      cases rest with
      | nil =>
          simp only [mapChildren, forest] at children
          exact ⟨annotation, shape, children.1⟩
      | cons next rest => simp only [mapChildren, forest, and_false] at children

variable [DecidableEq FullSyntax.Formula]

private theorem component_instance
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (name : String) (scheme : Ty) (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.node [component (context lib query).types name (encodeTy scheme)])) term) :
    ∃ rho : String → Ty,
      term = .node (literal name) [candidateRigid (substTy rho scheme)] ∧
      ∀ raw, variableSymbol raw ∈ variables (encodeTy scheme) →
        RawAdmitted (constructorCatalog lib query) (rho raw) := by
  obtain ⟨annotation, shape, child⟩ := singleton_child
    (SourceEqualityPCSGuard.holds formulas solver) name
    (generalize (context lib query).types (encodeTy scheme)) term accepted
  obtain ⟨rho, same, images⟩ := SourceSynthesisCurrentGeneralizeReification.generalize_instance
    formulas solver lib query scheme annotation child
  exact ⟨rho, by simpa only [same] using shape, images⟩

private theorem shape_fields (name : String) (typ : Ty) (term : Term Symbol)
    (same : term = .node (literal name) [candidateRigid typ]) :
    term.atPath [0] = some (candidateRigid typ) ∧
      Projection literal Prod.fst term (.var name) ∧
      toProgram literal Prod.fst term = .var name ∧
      (toProgram literal Prod.fst term).components = 1 := by
  subst term
  exact ⟨rfl, .component _ _, rfl, rfl⟩

/-- Actual current size-one acceptance retains ordinary typing and its original binding origin. -/
theorem size_one_typed
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool}
    {expression : Expression} {term : Term Symbol}
    (member : expression ∈ termsRows (context lib query) asArgument 1)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ name typ,
      term = .node (literal name) [candidateRigid typ] ∧
      Typed lib query (.var name) typ ∧
      term.atPath [0] = some (candidateRigid typ) ∧
      Projection literal Prod.fst term (.var name) ∧
      toProgram literal Prod.fst term = .var name ∧
      (toProgram literal Prod.fst term).components = 1 ∧
      ((∃ entry ∈ lib.libraryGroups, ∃ rho : String → Ty,
          name = entry.1 ∧ typ = substTy rho entry.2.1 ∧
          ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2.1) →
            RawAdmitted (constructorCatalog lib query) (rho raw)) ∨
       (asArgument = true ∧ ∃ entry ∈ lib.libraryArgumentOnly, ∃ rho : String → Ty,
          name = entry.1 ∧ typ = substTy rho entry.2 ∧
          ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2) →
            RawAdmitted (constructorCatalog lib query) (rho raw)) ∨
       ((name, typ) ∈ queryBindings query ∧
          queryLookup query.queryArguments name = some typ)) := by
  rw [SourceSynthesisFirstOrderConstruction.termsRows_one] at member
  rcases List.mem_append.mp member with base | extra
  · rcases List.mem_cons.mp base with same | later
    · subst expression
      obtain ⟨row, included, observed⟩ := selected_row
        (SourceEqualityPCSGuard.holds formulas solver) _ term accepted
      change row ∈ ((queryBindings query).map fun entry =>
        (entry.1, (.mk entry.1 top [typeNode entry.2] : Row))).map Prod.snd at included
      rw [List.map_map] at included
      obtain ⟨entry, binding, rfl⟩ := List.mem_map.mp included
      obtain ⟨annotation, shape, child⟩ := singleton_child
        (SourceEqualityPCSGuard.holds formulas solver) entry.1 (typeNode entry.2) term observed
      have rigid := SourceSynthesisCurrentRigidTypeReification.current_typeNode_only
        (SourceEqualityPCSGuard.holds formulas solver) entry.2 annotation child
      have exactShape : term = .node (literal entry.1) [candidateRigid entry.2] := by
        simpa only [rigid] using shape
      have last := queryBindings_member query entry.1 entry.2 binding
      obtain ⟨path, projected, decoded, counted⟩ := shape_fields entry.1 entry.2 term exactShape
      exact ⟨entry.1, entry.2, exactShape, .queryArgument last, path, projected, decoded, counted,
        Or.inr (Or.inr ⟨binding, last⟩)⟩
    · have same := List.mem_singleton.mp later
      subst expression
      obtain ⟨row, included, observed⟩ := selected_row
        (SourceEqualityPCSGuard.holds formulas solver) _ term accepted
      change row ∈ (lib.libraryGroups.map fun entry =>
        (entry.1, component (context lib query).types entry.1 (encodeTy entry.2.1))).map Prod.snd at included
      rw [List.map_map] at included
      obtain ⟨entry, binding, rfl⟩ := List.mem_map.mp included
      obtain ⟨rho, shape, images⟩ := component_instance formulas solver lib query
        entry.1 entry.2.1 term observed
      obtain ⟨path, projected, decoded, counted⟩ :=
        shape_fields entry.1 (substTy rho entry.2.1) term shape
      exact ⟨entry.1, substTy rho entry.2.1, shape, .group entry binding rho,
        path, projected, decoded, counted, Or.inl ⟨entry, binding, rho, rfl, rfl, images⟩⟩
  · cases asArgument with
    | false => cases extra
    | true =>
        have same := List.mem_singleton.mp extra
        subst expression
        obtain ⟨row, included, observed⟩ := selected_row
          (SourceEqualityPCSGuard.holds formulas solver) _ term accepted
        change row ∈ lib.libraryArgumentOnly.map (fun entry =>
          component (context lib query).types entry.1 (encodeTy entry.2)) at included
        obtain ⟨entry, binding, rfl⟩ := List.mem_map.mp included
        obtain ⟨rho, shape, images⟩ := component_instance formulas solver lib query
          entry.1 entry.2 term observed
        obtain ⟨path, projected, decoded, counted⟩ :=
          shape_fields entry.1 (substTy rho entry.2) term shape
        exact ⟨entry.1, substTy rho entry.2, shape, .argumentOnly entry binding rho,
          path, projected, decoded, counted,
          Or.inr (Or.inl ⟨rfl, entry, binding, rho, rfl, rfl, images⟩)⟩

end MicroCFTA.SourceSynthesisCurrentLeafTyping
