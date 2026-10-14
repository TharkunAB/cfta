import MicroCFTA.SourceSizedLiquidAmbientRepair
import MicroCFTA.SourceReadLogicalIntegerCore

/-!
# Historical collision with an implicit ambient name

The old preflight permits a generated value to use a free ambient name.
That alias makes a query valid only because the ambient assumption refers
to the same name. A distinct generated name does not have that conclusion.
The repaired preflight returns Unknown for the collision.
-/

namespace MicroCFTA.SourceSizedLiquidAmbientCollision

open FullSyntax SolverAdapter SourceSizedLiquidProgram
open SourceSizedLiquidAmbient SourceReadLogicalIntegerCore

/-- The first generated name occurs only in the ambient assumption. -/
def ambientName : Name := "__cfta_actual_0"

/-- A separate generated name does not alias that assumption. -/
def separateName : Name := "__cfta_actual_1"

/-- The implicit ambient value equals zero. -/
def assumptions : List Formula := [.atom .eq (.var ambientName) (.lit 0)]

/-- A generated value is tested for equality with zero. -/
def query (name : Name) : Query := ⟨[(name, "actual")], .top, .atom .eq (.var name) (.lit 0)⟩

/-- The historical preflight accepts the colliding generated name. -/
theorem old_accepts_collision :
    (SolverAdapter.prepareQuery [] (query ambientName).bindings assumptions
      (query ambientName).antecedent (query ambientName).consequent).isSome = true := by decide

/-- The historical alias is entailed by the unchanged ambient assumption. -/
theorem aliased_entailed : Meaning integerTarget [] assumptions (query ambientName) := by
  intro env domain assumed antecedent
  simpa only [assumptions, holdsAll, and_true, query] using assumed

/-- Independent fresh values do not inherit the ambient variable's equality. -/
theorem separate_not_entailed : ¬Meaning integerTarget [] assumptions (query separateName) := by
  intro entailed
  let env : Name → Int := fun name => if name = separateName then 1 else 0
  have domain : Domain integerTarget [] assumptions (query separateName) env := by
    refine ⟨?_, ?_, ?_⟩
    · intro binding member
      have equal : binding = ("__cfta_value", FormulaLowering.TargetSort.int) := by simpa [declarations, valueName] using member
      subst binding
      trivial
    · intro binding member
      have equal : binding = (separateName, "actual") := by simpa [query] using member
      subst binding
      trivial
    · intro name free notAmbient notGenerated
      trivial
  have assumed : holdsAll (FormulaLowering.sourceModel integerTarget) env assumptions := by
    simp [assumptions, holdsAll, Holds, evaluateTerm, FormulaLowering.sourceModel,
      integerTarget, CoreFormula.evalRelation, env, ambientName, separateName]
  have falseEquality := entailed env domain assumed (by simp [query, Holds])
  simp [query, Holds, evaluateTerm, FormulaLowering.sourceModel, integerTarget,
    CoreFormula.evalRelation, env] at falseEquality

/-- The repair rejects the precise free-name collision before an external query. -/
theorem repaired_rejects_collision :
    SourceSizedLiquidAmbientRepair.prepareQuery [] assumptions (query ambientName) = none := by
  simp [SourceSizedLiquidAmbientRepair.prepareQuery, SourceSizedLiquidAmbientRepair.collides,
    assumptions, query, partsNames, formulaNames, termNames]

/-- The repaired source maps that preflight failure to returned Unknown. -/
theorem repaired_unknown (milliseconds : Int) (check : Prepared → Nat → Attempt → Prop) :
    SourceSizedLiquidAmbientRepair.Call [] assumptions milliseconds check (query ambientName) 1 (.returned .unknown) :=
  .preflight repaired_rejects_collision

/-- The repair preserves the request for the separate generated name. -/
theorem repaired_preserves_separate :
    SourceSizedLiquidAmbientRepair.prepareQuery [] assumptions (query separateName) =
      SolverAdapter.prepareQuery [] (query separateName).bindings assumptions
        (query separateName).antecedent (query separateName).consequent := by
  apply SourceSizedLiquidAmbientRepair.unchanged
  simp [query, assumptions, partsNames, formulaNames, termNames, ambientName, separateName]

end MicroCFTA.SourceSizedLiquidAmbientCollision
