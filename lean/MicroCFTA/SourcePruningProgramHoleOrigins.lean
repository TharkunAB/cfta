import MicroCFTA.SourcePruningPositions
import MicroCFTA.SourcePruningProgramSemantics

/-!
# Original program positions at actual fragment holes

The source program-hole traversal follows only function, argument and filter
program children. Each selected hole retains its own inspected program
positions in the filled fragment. Annotation holes are not selected here.
-/
namespace MicroCFTA.SourcePruningPositions
open Language Fragments SourcePruningTemplates
attribute [local instance] FormulaExecutable.formulaDecidableEq

/-- An inspected program below an actual program hole occurs in the filled fragment. -/
theorem programHoles_programAt (assignment : Nat → Term Symbol) (fragment : Fragment Symbol) :
    ∀ uv ∈ programHoles false fragment, ∀ program,
      ProgramAt (assignment uv) program → ProgramAt (fill assignment fragment) program := by
  induction fragment using Fragment.rec
    (motive_2 := fun children => ∀ child ∈ children,
      ∀ uv ∈ programHoles false child, ∀ program,
        ProgramAt (assignment uv) program → ProgramAt (fill assignment child) program) with
  | hole other =>
      intro uv member program position
      have same : uv = other := by simpa only [programHoles_hole, List.mem_singleton] using member
      subst uv
      simpa only [fill] using position
  | node symbol children ih =>
      intro uv member program position
      cases children with
      | nil => simp [programHoles] at member
      | cons first rest =>
          cases rest with
          | nil => simp [programHoles] at member
          | cons second rest =>
              cases rest with
              | nil =>
                  by_cases filtered : symbol = ("filter", FullSyntax.Formula.top)
                  · subst symbol
                    rw [programHoles_filter] at member
                    simp only [fill, List.map_cons, List.map_nil]
                    exact .filter _ _ _ (ih second (by simp) uv member program position)
                  · simp [programHoles, filtered] at member
              | cons third rest =>
                  cases rest with
                  | nil => simp [programHoles] at member
                  | cons fourth rest =>
                      cases rest with
                      | cons fifth rest => simp [programHoles] at member
                      | nil =>
                          by_cases applied : symbol = ("app", FullSyntax.Formula.top)
                          · subst symbol
                            rw [programHoles_app, List.mem_append] at member
                            simp only [fill, List.map_cons, List.map_nil]
                            rcases member with inFunction | inArgument
                            · exact .function _ _ _ _ _
                                (ih third (by simp) uv inFunction program position)
                            · exact .argument _ _ _ _ _
                                (ih fourth (by simp) uv inArgument program position)
                          · rw [programHoles_other_four symbol first second third fourth applied] at member
                            cases member
  | nil =>
      rename_i child member _uv _inside _program _position
      cases member
  | cons child children first rest =>
      rename_i selected member uv inside program position
      rcases List.mem_cons.mp member with same | member
      · subst selected
        exact first uv inside program position
      · exact rest selected member uv inside program position

/-- Original template avoidance holds at each actual program-hole assignment. -/
theorem programHoles_avoids (assignment : Nat → Term Symbol)
    (templates : List (Template.Pattern Symbol)) (fragment : Fragment Symbol) (uv : Nat)
    (member : uv ∈ programHoles false fragment)
    (avoids : Avoids templates (fill assignment fragment)) : Avoids templates (assignment uv) := by
  intro program position pattern listed
  exact avoids program (programHoles_programAt assignment fragment uv member program position) pattern listed

end MicroCFTA.SourcePruningPositions
