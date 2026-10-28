import MicroCFTA.SourcePruningProgramHoleOrigins
import MicroCFTA.SourcePruningStructuralTemplateMeaning

/-!
# Scope of original program-position provenance

An encoded constant permits an arbitrary annotation term. The actual source
position traversal marks its annotation hole as a type hole. Program
positions in that assignment need not be positions in the complete constant.
This pure witness is not a native execution or a public Haskell defect.
-/
namespace MicroCFTA.SourcePruningPositions
open Language Fragments SourcePruningTemplates
attribute [local instance] FormulaExecutable.formulaDecidableEq

/-- Root encoding does not turn an actual annotation hole into an original program position. -/
theorem encoded_type_hole_not_program_origin :
    ∃ (assignment : Nat → Term Symbol) (fragment : Fragment Symbol),
      ProgramEncoding (fill assignment fragment) ∧
      1 ∈ typePositions false fragment [] ∧
      1 ∉ programHoles false fragment ∧
      ProgramAt (assignment 1) (assignment 1) ∧
      ¬ ProgramAt (fill assignment fragment) (assignment 1) := by
  let leaf : Term Symbol := .node ("type", FullSyntax.Formula.top) []
  let application : Term Symbol :=
    .node ("app", FullSyntax.Formula.top) [leaf, leaf, leaf, leaf]
  let assignment : Nat → Term Symbol := fun _ => application
  let fragment : Fragment Symbol := .node ("constant", FullSyntax.Formula.top) [.hole 1]
  have filled : fill assignment fragment =
      .node ("constant", FullSyntax.Formula.top) [application] := by
    simp only [fragment, fill, List.map_cons, List.map_nil, assignment]
  refine ⟨assignment, fragment, ?_, ?_, ?_, ?_, ?_⟩
  · rw [filled]
    exact .constant _ _
  · simp [fragment, typePositions, EnumerationBuilderCaches.canonicalIds_member]
  · simp [fragment, programHoles]
  · exact .application _ _ _ _
  · intro position
    rw [filled] at position
    cases position

end MicroCFTA.SourcePruningPositions
