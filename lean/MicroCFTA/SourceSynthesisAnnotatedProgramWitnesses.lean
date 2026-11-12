import MicroCFTA.SourceSynthesisFiniteTypeWitnesses
import MicroCFTA.SourceSynthesisFirstOrderConstruction

/-!
# Joint annotated Program constructors

Current child memberships and annotation paths determine all application
and filter equalities. Application requires a structural universe witness
only for its result annotation. Each component occurrence can instantiate
its own scheme. Rigid arguments and goals need no universe admission.

These laws do not select source-table rows or prove original construction
success. The existing Program projection constructors retain these layouts.
-/
namespace MicroCFTA.SourceSynthesisAnnotatedProgramWitnesses
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard variables generalize)
open SourceSynthesisFirstOrderConstruction (Expression component application ofType)
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

private theorem pair_sat (term : Term Symbol) (left right : List Nat) (common : Term Symbol)
    (first : term.atPath left = some common) (second : term.atPath right = some common) :
    EqualityNormalize.ClassSat term [left, right] := by
  intro p included q member _different
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included member
  rcases included with rfl | rfl <;> rcases member with rfl | rfl
  · exact ⟨common, first, first⟩
  · exact ⟨common, first, second⟩
  · exact ⟨common, second, first⟩
  · exact ⟨common, second, second⟩

private theorem annotation_path {term annotation : Term Symbol}
    (found : term.atPath [0] = some annotation) (path : List Nat) :
    term.atPath (0 :: path) = annotation.atPath path := by
  change term.atPath ([0] ++ path) = _
  rw [Language.atPath_append, found, Option.bind_some]

private theorem application_equalities (function argument domain codomain : Term Symbol)
    (functionType : function.atPath [0] =
      some (.node (literal "->") [marker, domain, codomain]))
    (argumentType : argument.atPath [0] = some domain) :
    EqualityNormalize.Satisfies (.node (literal "app") [codomain, marker, function, argument])
      [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]] := by
  have first : function.atPath [0, 0] = some marker := by
    simpa only [Term.atPath, List.getElem?_cons_zero, Option.bind_some] using annotation_path functionType [0]
  have second : function.atPath [0, 1] = some domain := by
    simpa only [Term.atPath, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some] using
      annotation_path functionType [1]
  have third : function.atPath [0, 2] = some codomain := by
    simpa only [Term.atPath, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some] using
      annotation_path functionType [2]
  intro paths included
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl | rfl
  · refine pair_sat _ _ _ marker rfl ?_
    change function.atPath [0, 0] = some marker
    exact first
  · refine pair_sat _ _ _ domain ?_ ?_
    · change argument.atPath [0] = some domain
      exact argumentType
    · change function.atPath [0, 1] = some domain
      exact second
  · refine pair_sat _ _ _ codomain rfl ?_
    change function.atPath [0, 2] = some codomain
    exact third

private theorem node_member (holds : Guard → Term Symbol → Bool)
    (name : String) (guard : Guard) (children : List Expression) (terms : List (Term Symbol))
    (accepted : forest holds [] (mapChildren literal children) terms)
    (held : holds guard (.node (literal name) terms) = true) :
    evaluate holds [] (mapSyntax literal (.node [.mk name guard children]))
      (.node (literal name) terms) := by
  simp only [mapSyntax, mapEdges]
  rw [evaluate]
  refine ⟨⟨.mk (literal name) guard (mapChildren literal children), List.mem_cons_self⟩, ?_⟩
  rw [edgeMeaning]
  exact ⟨terms, rfl, accepted, held⟩

variable [DecidableEq FullSyntax.Formula]

private theorem eqGuard_true (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (classes : EqualityNormalize.Constraints) (term : Term Symbol)
    (satisfied : EqualityNormalize.Satisfies term classes) :
    SourceEqualityPCSGuard.holds formulas solver (eqGuard classes) term = true := by
  apply (SourceEqualityPCSGuard.holds_exact formulas solver (eqGuard classes) term).mpr
  constructor
  · rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
    exact (SourceEqualityPCSGuard.normalize_sat classes term).mpr satisfied
  · exact ((SourceEqualityPCSGuard.holds_exact formulas solver
      SourceEqualityConstraintConstructors.top term).mp
        (SourceEqualityPCSConstructors.top_true formulas solver term)).2

/-- Exact child annotations derive all three guards of an actual application. -/
theorem application_member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (catalog : List (String × Nat))
    (function argument : Expression) (functionTerm argumentTerm domain codomain : Term Symbol)
    (functionMember : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal function) functionTerm)
    (argumentMember : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal argument) argumentTerm)
    (functionType : functionTerm.atPath [0] =
      some (.node (literal "->") [marker, domain, codomain]))
    (argumentType : argumentTerm.atPath [0] = some domain)
    (admittedCodomain : TypeIn catalog codomain) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (application (allTypes top catalog) function argument))
      (.node (literal "app") [codomain, marker, functionTerm, argumentTerm]) := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  have topHeld := SourceEqualityPCSConstructors.top_true formulas solver
  have codomainMember := TypeIn.member holds topHeld admittedCodomain
  have markerMember : evaluate holds [] (mapSyntax literal (arrowMarker top)) marker :=
    node_member holds "(->)" top [] [] (by simp only [mapChildren, forest]) (topHeld _)
  apply node_member holds "app"
    (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
    [allTypes top catalog, arrowMarker top, function, argument]
    [codomain, marker, functionTerm, argumentTerm]
  · simp only [mapChildren, forest]
    exact ⟨codomainMember, markerMember, functionMember, argumentMember, True.intro⟩
  · exact eqGuard_true formulas solver _ _
      (application_equalities functionTerm argumentTerm domain codomain functionType argumentType)

/-- A matching current annotation derives the actual filter guard without universe admission. -/
theorem ofType_member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (candidates goal : Expression)
    (candidateTerm goalTerm : Term Symbol)
    (candidateMember : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal candidates) candidateTerm)
    (goalMember : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal goal) goalTerm)
    (annotation : candidateTerm.atPath [0] = some goalTerm) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (ofType candidates goal))
      (.node (literal "filter") [goalTerm, candidateTerm]) := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  apply node_member holds "filter" (eqGuard [[[0], [1, 0]]])
    [goal, candidates] [goalTerm, candidateTerm]
  · simp only [mapChildren, forest]
    exact ⟨goalMember, candidateMember, True.intro⟩
  · apply eqGuard_true formulas solver
    intro paths included
    have same := List.mem_singleton.mp included
    subst paths
    refine pair_sat _ _ _ goalTerm rfl ?_
    change candidateTerm.atPath [0] = some goalTerm
    exact annotation

/-- Each component occurrence accepts its own structurally admitted scheme instance. -/
theorem component_member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (catalog : List (String × Nat))
    (name : String) (typ : Ty) (substitution : String → Term Symbol)
    (images : ∀ key ∈ variables typ, TypeIn catalog (substitution key)) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.node [component (allTypes top catalog) name typ]))
      (.node (literal name) [SourceSynthesisGeneralizeFiniteInstances.instantiate substitution typ]) := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  apply node_member holds name top [generalize (allTypes top catalog) typ]
    [SourceSynthesisGeneralizeFiniteInstances.instantiate substitution typ]
  · simp only [mapChildren, forest]
    exact ⟨SourceSynthesisFiniteTypeWitnesses.generalize_member_of_TypeIn
      formulas solver catalog typ substitution images, True.intro⟩
  · exact SourceEqualityPCSConstructors.top_true formulas solver _

/-- A rigid argument accepts its exact finite type without universe admission. -/
theorem argument_member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (name : String) (typ : Ty) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.node [.mk name top [typeNode top typ]]))
      (.node (literal name) [rigidTerm typ]) := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  have topHeld := SourceEqualityPCSConstructors.top_true formulas solver
  apply node_member holds name top [typeNode top typ] [rigidTerm typ]
  · simp only [mapChildren, forest]
    exact ⟨SourceSynthesisFiniteTypeWitnesses.typeNode_member holds topHeld typ, True.intro⟩
  · exact topHeld _

end MicroCFTA.SourceSynthesisAnnotatedProgramWitnesses
