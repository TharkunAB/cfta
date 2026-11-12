import MicroCFTA.SourceSynthesisCurrentArrowReification
import MicroCFTA.SourceSynthesisCurrentRigidTypeReification

/-!
# Ordinary typing of the current application layout

The actual four-child forest supplies the internal marker.
The original application PCS classes determine arrow, domain and result types.
The child receipts retain the same terms, Programs and raw type annotations.
Type conversion uses the documented Fun/2 equivalence.
This result does not establish row induction or whole source soundness.
-/
namespace MicroCFTA.SourceSynthesisCurrentApplicationTyping
open Language
open InternedGuardedSyntax (evaluate forest)
open SourceSynthesisTypeSyntax (Ty Library Query arrowMarker)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisCurrentContext (context)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren)
open SourceSynthesisProgramTermSize (Program Projection)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisPr210TypeReflection (candidateRigid candidateRigid_eq_iff)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

private theorem pair_equal (term : Term Symbol) (left right : List Nat)
    (satisfied : EqualityNormalize.ClassSat term [left, right]) (different : left ≠ right) :
    term.atPath left = term.atPath right := by
  obtain ⟨common, first, second⟩ := satisfied left (by simp) right (by simp) different
  exact first.trans second.symm

private theorem annotation_path {term annotation : Term Symbol}
    (found : term.atPath [0] = some annotation) (path : List Nat) :
    term.atPath (0 :: path) = annotation.atPath path := by
  change term.atPath ([0] ++ path) = _
  rw [Language.atPath_append, found, Option.bind_some]

/-- Actual application fields and guards join the same ordinary child receipts. -/
theorem application_typed [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query)
    (functionExpression argumentExpression : Expression)
    (annotation actualMarker functionTerm argumentTerm : Term Symbol)
    (functionProgram argumentProgram : Program) (functionType argumentType : Ty)
    (children : forest (SourceEqualityPCSGuard.holds formulas solver) []
      (mapChildren literal [(context lib query).types, arrowMarker top,
        functionExpression, argumentExpression])
      [annotation, actualMarker, functionTerm, argumentTerm])
    (guardHeld : SourceEqualityPCSGuard.holds formulas solver
      (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
      (.node (literal "app") [annotation, actualMarker, functionTerm, argumentTerm]) = true)
    (functionTyped : Typed lib query functionProgram functionType)
    (functionProjection : Projection literal Prod.fst functionTerm functionProgram)
    (functionAnnotation : functionTerm.atPath [0] = some (candidateRigid functionType))
    (argumentTyped : Typed lib query argumentProgram argumentType)
    (argumentProjection : Projection literal Prod.fst argumentTerm argumentProgram)
    (argumentAnnotation : argumentTerm.atPath [0] = some (candidateRigid argumentType)) :
    ∃ resultType : Ty,
      Typed lib query (.app functionProgram argumentProgram) resultType ∧
      annotation = candidateRigid resultType ∧
      Projection literal Prod.fst
        (.node (literal "app") [annotation, actualMarker, functionTerm, argumentTerm])
        (.app functionProgram argumentProgram) := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let whole : Term Symbol :=
    .node (literal "app") [annotation, actualMarker, functionTerm, argumentTerm]
  have markerMember : evaluate holds [] (mapSyntax literal (arrowMarker top)) actualMarker := by
    have parts := children
    simp only [mapChildren, forest] at parts
    exact parts.2.1
  have markerSame : actualMarker = marker := by
    have exactMarker := SourceSynthesisCurrentRigidTypeReification.typeNode_only holds
      (.tCons "(->)" []) actualMarker
      (by simpa only [SourceSynthesisTypeSyntax.typeNode, arrowMarker, List.map_nil] using markerMember)
    simpa only [SourceSynthesisFiniteTypeWitnesses.rigidTerm, List.map_nil] using exactMarker
  have satisfied : EqualityNormalize.Satisfies whole
      [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]] := by
    have raw := ((SourceEqualityPCSGuard.holds_exact formulas solver _ whole).mp guardHeld).1
    rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source] at raw
    exact (SourceEqualityPCSGuard.normalize_sat _ whole).mp raw
  have markerPair := pair_equal whole [1] [2, 0, 0]
    (satisfied _ (by simp)) (by decide)
  have functionMarker : functionTerm.atPath [0, 0] = some marker := by
    simpa only [whole, Term.atPath, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.bind_some, markerSame] using markerPair.symm
  have markerAt : (candidateRigid functionType).atPath [0] = some marker :=
    (annotation_path functionAnnotation [0]).symm.trans functionMarker
  obtain ⟨domain, codomain, functionEquivalent, functionShape⟩ :=
    SourceSynthesisCurrentArrowReification.marker_child_arrow functionType markerAt
  have domainPath : functionTerm.atPath [0, 1] = some (candidateRigid domain) := by
    rw [annotation_path functionAnnotation [1], functionShape]
    simp only [Term.atPath, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some]
  have resultPath : functionTerm.atPath [0, 2] = some (candidateRigid codomain) := by
    rw [annotation_path functionAnnotation [2], functionShape]
    simp only [Term.atPath, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some]
  have domainPair := pair_equal whole [3, 0] [2, 0, 1]
    (satisfied _ (by simp)) (by decide)
  have domainSame : argumentTerm.atPath [0] = functionTerm.atPath [0, 1] := by
    simpa only [whole, Term.atPath, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.bind_some] using domainPair
  have encodedDomain : candidateRigid argumentType = candidateRigid domain :=
    Option.some.inj (argumentAnnotation.symm.trans (domainSame.trans domainPath))
  have resultPair := pair_equal whole [0] [2, 0, 2]
    (satisfied _ (by simp)) (by decide)
  have resultSame : some annotation = functionTerm.atPath [0, 2] := by
    simpa only [whole, Term.atPath, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.bind_some] using resultPair
  have annotationSame : annotation = candidateRigid codomain :=
    Option.some.inj (resultSame.trans resultPath)
  have functionArrow : Typed lib query functionProgram (.tFun domain codomain) :=
    .conversion functionTyped functionEquivalent
  have argumentDomain : Typed lib query argumentProgram domain :=
    .conversion argumentTyped ((candidateRigid_eq_iff argumentType domain).mp encodedDomain)
  exact ⟨codomain, .application functionArrow argumentDomain, annotationSame,
    .application annotation actualMarker functionProjection argumentProjection⟩

end MicroCFTA.SourceSynthesisCurrentApplicationTyping
