import MicroCFTA.SourceSynthesisProgramTermSize
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourcePruningPartialMatchSemantics
import MicroCFTA.SourcePruningPositions

/-!
# Decoder preservation for projected partial Programs

Every completion preserves the current projected Program.
Opaque Type subtrees remain unrestricted. Program positions retain their concrete layouts.
The result does not require a completion to exist.
It does not derive Program roles from an enumeration cache or callback.
-/
namespace MicroCFTA.SourceSynthesisPartialProgramDecoder
open Language
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourcePruningPartialMatch (Completes)
open SourcePruningPositions (openProgram)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "PartialTerm" => SourcePruningTemplates.PartialTerm
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private theorem openProgram_concrete (partialTerm : PartialTerm) (symbol : Symbol)
    (terms : List (Term Symbol)) (nonempty : terms ≠ [])
    (same : openProgram true partialTerm = .node symbol terms) :
    ∃ children, partialTerm = .node (.concrete symbol) children ∧
      children.map (openProgram true) = terms := by
  cases partialTerm with
  | node head children =>
      cases head with
      | concrete actual =>
          rw [SourcePruningPositions.openProgram_type_node] at same
          obtain ⟨symbolSame, childrenSame⟩ := Term.node.inj same
          subst actual
          exact ⟨children, rfl, childrenSame⟩
      | hole uv =>
          rw [SourcePruningPositions.openProgram_type_hole] at same
          exact False.elim (nonempty (Term.node.inj same).2.symm)
      | truncated =>
          rw [SourcePruningPositions.openProgram_truncated] at same
          exact False.elim (nonempty (Term.node.inj same).2.symm)

private theorem completes_concrete {assignment : Nat → Term Symbol} {symbol : Symbol}
    {partials : List PartialTerm} {full : Term Symbol}
    (completed : Completes assignment (.node (.concrete symbol) partials) full) :
    ∃ terms, full = .node symbol terms ∧ All₂ (Completes assignment) partials terms := by
  cases completed
  exact ⟨_, rfl, by assumption⟩

private theorem projection_completes {term : Term Symbol} {program : Program}
    (projected : Projection literal Prod.fst term program) :
    ∀ partialTerm, openProgram true partialTerm = term →
      ∀ (assignment : Nat → Term Symbol) full, Completes assignment partialTerm full →
        Projection literal Prod.fst full program := by
  induction projected with
  | component symbol annotation =>
      intro partialTerm same assignment full completed
      obtain ⟨partials, rfl, mapped⟩ := openProgram_concrete partialTerm _ _ (by simp) same
      obtain ⟨partialAnnotation, rfl, _annotationSame⟩ := List.map_eq_singleton_iff.mp mapped
      obtain ⟨terms, rfl, paired⟩ := completes_concrete completed
      cases paired with
      | cons _ tail =>
          cases tail
          exact .component _ _
  | application annotation marker first second firstIH secondIH =>
      intro partialTerm same assignment full completed
      obtain ⟨partials, rfl, mapped⟩ := openProgram_concrete partialTerm _ _ (by simp) same
      obtain ⟨partialAnnotation, tail, rfl, _annotationSame, mapped⟩ := List.map_eq_cons_iff.mp mapped
      obtain ⟨partialMarker, tail, rfl, _markerSame, mapped⟩ := List.map_eq_cons_iff.mp mapped
      obtain ⟨partialFunction, tail, rfl, functionSame, mapped⟩ := List.map_eq_cons_iff.mp mapped
      obtain ⟨partialArgument, rfl, argumentSame⟩ := List.map_eq_singleton_iff.mp mapped
      obtain ⟨terms, rfl, paired⟩ := completes_concrete completed
      cases paired with
      | cons _ tail =>
          cases tail with
          | cons _ tail =>
              cases tail with
              | cons functionComplete tail =>
                  cases tail with
                  | cons argumentComplete tail =>
                      cases tail
                      exact .application _ _
                        (firstIH _ functionSame assignment _ functionComplete)
                        (secondIH _ argumentSame assignment _ argumentComplete)
  | filter goal candidate ih =>
      intro partialTerm same assignment full completed
      obtain ⟨partials, rfl, mapped⟩ := openProgram_concrete partialTerm _ _ (by simp) same
      obtain ⟨partialGoal, tail, rfl, _goalSame, mapped⟩ := List.map_eq_cons_iff.mp mapped
      obtain ⟨partialBody, rfl, bodySame⟩ := List.map_eq_singleton_iff.mp mapped
      obtain ⟨terms, rfl, paired⟩ := completes_concrete completed
      cases paired with
      | cons _ tail =>
          cases tail with
          | cons bodyComplete tail =>
              cases tail
              exact .filter _ (ih _ bodySame assignment _ bodyComplete)

/-- Every completion of the current projected partial syntax retains its same Program decoder. -/
theorem completion_decoder_of_projection [DecidableEq Symbol]
    (partialTerm : SourcePruningTemplates.PartialTerm)
    (program : SourceSynthesisProgramTermSize.Program)
    (projected : SourceSynthesisProgramTermSize.Projection literal Prod.fst
      (SourcePruningPositions.openProgram true partialTerm) program) :
    ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
      SourcePruningPartialMatch.Completes assignment partialTerm full →
      SourceSynthesisProgramTermSize.Projection literal Prod.fst full program ∧
      SourceSynthesisProgramTermSize.toProgram literal Prod.fst full =
        SourceSynthesisProgramTermSize.toProgram literal Prod.fst
          (SourcePruningPositions.openProgram true partialTerm) := by
  intro assignment full completed
  have fullProjected := projection_completes projected partialTerm rfl assignment full completed
  exact ⟨fullProjected, fullProjected.toProgram_eq.trans projected.toProgram_eq.symm⟩

end MicroCFTA.SourceSynthesisPartialProgramDecoder
