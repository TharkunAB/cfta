import MicroCFTA.SourcePruningPartialMatchSemantics
import MicroCFTA.SourcePruningTemplateIndexMeaning
import MicroCFTA.SourcePruningResumeRefutation

/-!
# Complete programs selected by actual partial matching

Program positions follow application function and argument children.
Filter wrappers expose only their program child.
Annotations do not add program positions.
-/
namespace MicroCFTA.SourcePruningTemplates
open Language EnumerationState SourcePruningPartialMatch
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq

/-- A complete program occurs at a position inspected by the source callback. -/
inductive ProgramAt : Term Symbol → Term Symbol → Prop where
  /-- The complete application is a program position. -/
  | application (annotation marker function argument : Term Symbol) :
      ProgramAt (.node ("app", FullSyntax.Formula.top) [annotation, marker, function, argument])
        (.node ("app", FullSyntax.Formula.top) [annotation, marker, function, argument])
  /-- A function child retains its program positions. -/
  | function (annotation marker function argument program : Term Symbol) :
      ProgramAt function program →
      ProgramAt (.node ("app", FullSyntax.Formula.top) [annotation, marker, function, argument]) program
  /-- An argument child retains its program positions. -/
  | argument (annotation marker function argument program : Term Symbol) :
      ProgramAt argument program →
      ProgramAt (.node ("app", FullSyntax.Formula.top) [annotation, marker, function, argument]) program
  /-- A filter retains its program child positions. -/
  | filter (annotation term program : Term Symbol) :
      ProgramAt term program → ProgramAt (.node ("filter", FullSyntax.Formula.top) [annotation, term]) program

/-- Every original forbidden template fails at every source program position. -/
def Avoids (templates : List (Template.Pattern Symbol)) (term : Term Symbol) : Prop :=
  ∀ program, ProgramAt term program → ∀ pattern ∈ templates, ¬ Template.Matches pattern program

/-- Each actually selected partial program completes at an original program position. -/
theorem programs_complete (assignment : Nat → Term Symbol)
    (observedTerm program : PartialTerm) (whole : Term Symbol)
    (completed : Completes assignment observedTerm whole) (member : program ∈ programs observedTerm) :
    ∃ fullProgram, ProgramAt whole fullProgram ∧ Completes assignment program fullProgram := by
  induction observedTerm using Term.rec
    (motive_2 := fun children => ∀ terms,
      All₂ (Completes assignment) children terms →
      All₂ (fun child full => ∀ selected ∈ programs child,
        ∃ fullProgram, ProgramAt full fullProgram ∧ Completes assignment selected fullProgram) children terms)
    generalizing program whole with
  | node partialSymbol children ih =>
      cases partialSymbol with
      | hole uv => simp only [programs, List.not_mem_nil] at member
      | truncated => simp only [programs, List.not_mem_nil] at member
      | concrete symbol =>
          cases completed with
          | concrete symbol children terms childCompletions =>
              have related := ih terms childCompletions
              cases children with
              | nil => simp only [programs, List.not_mem_nil] at member
              | cons first children =>
                  cases children with
                  | nil => simp only [programs, List.not_mem_nil] at member
                  | cons second children =>
                      cases children with
                      | nil =>
                          by_cases isFilter : symbol = ("filter", FullSyntax.Formula.top)
                          · subst symbol
                            simp only [programs, ↓reduceIte] at member
                            cases related with
                            | cons _ tail =>
                                cases tail with
                                | cons secondRelated tail =>
                                    cases tail
                                    obtain ⟨fullProgram, atProgram, fills⟩ := secondRelated program member
                                    exact ⟨fullProgram, .filter _ _ _ atProgram, fills⟩
                          · simp only [programs, isFilter, ↓reduceIte, List.not_mem_nil] at member
                      | cons third children =>
                          cases children with
                          | nil => simp only [programs, List.not_mem_nil] at member
                          | cons fourth children =>
                              cases children with
                              | nil =>
                                  by_cases isApp : symbol = ("app", FullSyntax.Formula.top)
                                  · subst symbol
                                    simp only [programs, ↓reduceIte] at member
                                    cases related with
                                    | cons _ tail =>
                                        cases tail with
                                        | cons _ tail =>
                                            cases tail with
                                            | cons functionRelated tail =>
                                                cases tail with
                                                | cons argumentRelated tail =>
                                                    cases tail
                                                    rcases List.mem_cons.mp member with same | selected
                                                    · subst program
                                                      exact ⟨_, .application _ _ _ _,
                                                        .concrete _ _ _ childCompletions⟩
                                                    · rcases List.mem_append.mp selected with inFunction | inArgument
                                                      · obtain ⟨fullProgram, atProgram, fills⟩ := functionRelated program inFunction
                                                        exact ⟨fullProgram, .function _ _ _ _ _ atProgram, fills⟩
                                                      · obtain ⟨fullProgram, atProgram, fills⟩ := argumentRelated program inArgument
                                                        exact ⟨fullProgram, .argument _ _ _ _ _ atProgram, fills⟩
                                  · simp only [programs, isApp, ↓reduceIte, List.not_mem_nil] at member
                              | cons fifth rest => simp only [programs, List.not_mem_nil] at member
  | nil =>
      rename_i terms related
      cases related
      exact .nil
  | cons child children first rest =>
      rename_i terms related
      cases related with
      | cons firstCompletes restCompletes =>
          exact .cons (first _ firstCompletes) (rest _ restCompletes)

/-- Actual new pending groups retain the original complete program's template refutation. -/
theorem startMatches_refutes (assignment : Nat → Term Symbol)
    (templates : List (Template.Pattern Symbol)) (observedTerm : PartialTerm) (whole : Term Symbol)
    (completed : Completes assignment observedTerm whole) (avoids : Avoids templates whole)
    (pending : Pending Symbol) (member : some pending ∈ startMatches templates observedTerm) :
    SourcePruningResume.Refutes assignment pending := by
  unfold startMatches at member
  obtain ⟨program, selected, member⟩ := List.mem_flatMap.mp member
  obtain ⟨pattern, indexed, matched⟩ := List.mem_map.mp member
  obtain ⟨fullProgram, atProgram, fills⟩ := programs_complete assignment observedTerm program whole completed selected
  exact matchPartial_refutes assignment pattern program fullProgram pending fills matched
    (avoids fullProgram atProgram pattern (indexTemplates_mem templates program pattern indexed))

end MicroCFTA.SourcePruningTemplates
