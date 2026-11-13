import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SourceSynthesisProgramTermSize

namespace MicroCFTA.SourceSynthesisCurrentZeroProgramObstruction

private theorem components_pos (program : SourceSynthesisProgramTermSize.Program) :
    0 < program.components := by
  induction program with
  | var _ => exact Nat.zero_lt_succ 0
  | app function argument first second =>
      change 0 < function.components + argument.components
      omega

/-- Source construction succeeds at size zero. No Program has zero components. -/
theorem size_zero_frontend_without_program
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query) :
    ∃ expression : SourceSynthesisFirstOrderConstruction.Expression,
      SourceSynthesisCurrentConstruction.firstOrderRaw lib query (0 : Int) = .ok expression ∧
      ¬∃ program : SourceSynthesisProgramTermSize.Program,
        program.components = (0 : Int).toNat := by
  obtain ⟨expression, returned⟩ :=
    SourceSynthesisCurrentConstruction.firstOrderRaw_total lib query (0 : Int) (by decide)
  refine ⟨expression, returned, ?_⟩
  rintro ⟨program, counted⟩
  have positive := components_pos program
  change program.components = 0 at counted
  omega

end MicroCFTA.SourceSynthesisCurrentZeroProgramObstruction
