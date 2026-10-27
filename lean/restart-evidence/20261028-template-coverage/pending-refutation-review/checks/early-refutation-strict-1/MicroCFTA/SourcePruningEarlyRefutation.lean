import MicroCFTA.SourcePruningProgramSemantics
import MicroCFTA.SourcePruningStructuralTemplateMeaning

/-!
# Early rejection preserves original template avoidance

The original complete fragment fixes the meaning of every raw hole.
The source program encoding justifies the structural template conversion.
-/
namespace MicroCFTA.SourcePruningTemplates
open Language Fragments EnumerationState SourcePruningPartialMatch
attribute [local instance] FormulaExecutable.formulaDecidableEq

/-- The raw fragment view completes to the original assigned fragment. -/
theorem fragmentTerm_completes (assignment : Nat → Term Symbol) (fragment : Fragment Symbol) :
    Completes assignment (fragmentTerm fragment) (fill assignment fragment) := by
  induction fragment using Fragment.rec
    (motive_2 := fun children => All₂ (Completes assignment)
      (children.map fragmentTerm) (children.map (fill assignment))) with
  | hole uv => exact .hole uv
  | node symbol children completed => exact .concrete symbol _ _ completed
  | nil => exact .nil
  | cons child children first rest => exact .cons first rest

/-- Original template avoidance prevents the actual structural early rejection. -/
theorem rejectEarly_false (assignment : Nat → Term Symbol)
    (templates : List (Template.Pattern Symbol)) (fragment : Fragment Symbol)
    (avoids : Avoids templates (fill assignment fragment))
    (encoded : ∀ program, ProgramAt (fill assignment fragment) program → ProgramEncoding program) :
    rejectEarly templates fragment = false := by
  unfold rejectEarly
  split
  · apply List.any_eq_false.mpr
    intro observedProgram selected
    apply List.any_eq_false.mpr
    intro early indexed accepted
    have earlyMember := indexTemplates_mem (templates.filterMap structuralTemplate) observedProgram early indexed
    obtain ⟨original, originalMember, converted⟩ := List.mem_filterMap.mp earlyMember
    obtain ⟨fullProgram, atProgram, completed⟩ := programs_complete assignment (fragmentTerm fragment)
      observedProgram (fill assignment fragment) (fragmentTerm_completes assignment fragment) selected
    cases matched : matchPartial early observedProgram with
    | none => simp only [matched, Bool.false_eq_true] at accepted
    | some pending =>
        cases pending with
        | nil =>
            have earlyMatches := matchPartial_complete_sound assignment early observedProgram fullProgram completed matched
            exact avoids fullProgram atProgram original originalMember
              (structuralTemplate_matches original early fullProgram converted (encoded fullProgram atProgram) earlyMatches)
        | cons first rest => simp only [matched, Bool.false_eq_true] at accepted
  · rfl

end MicroCFTA.SourcePruningTemplates
