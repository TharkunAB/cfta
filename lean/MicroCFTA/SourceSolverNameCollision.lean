import MicroCFTA.SourceSolverNameEncodingFixpoint
import MicroCFTA.SourceSolverNameSemantics
import MicroCFTA.SourceReadLogicalIntegerCore

/-!
# Quantified capture from the historical Fixpoint name collision

The free name 1 and bound name fix$1 had the same serialized spelling.
That collision changed a false universal equality into a true one.
A correct Unsat response for the changed assertion therefore produced an
incorrect Yes for the source query. The repaired codec preserves falsity.
No theorem here asserts that an external solver returns a chosen response.
-/
namespace MicroCFTA.SourceSolverNameCollision
open FormulaLowering SourceSolverNameSemantics SourceSolverNameEncoding
open SourceReadLogicalIntegerCore SolverAdapter

/-- The exact source query from the native collision reproduction. -/
def sourceFormula : FullSyntax.Formula :=
  .forall [("fix$1", .int)] (.atom .eq (.var "1") (.var "fix$1"))

/-- The lowered universal equality retains distinct free and bound names. -/
def formula : Formula :=
  .forall [("fix$1", .int)] (.atom .eq (.variable "1") (.variable "fix$1"))

/-- The source formula lowers to this target formula without simplification. -/
theorem lowered : lowerFormula sourceFormula = formula := by
  simp [sourceFormula, formula, lowerFormula, lowerTerm, lowerSort]

/-- Choosing the free integer plus one refutes the original query in every environment. -/
theorem original_false (env : FullSyntax.Name → Int) : ¬Holds integerTarget env formula := by
  intro assumed
  simp only [formula, Holds, allBound] at assumed
  have counterexample := assumed (env "1" + 1) trivial
  simp [evaluate, integerTarget, CoreFormula.evalRelation, FullSyntax.update] at counterexample
  omega

/-- Historical serialization captures the free name and makes the query universally true. -/
theorem historical_true (env : FullSyntax.Name → Int) :
    Holds integerTarget env (renameFormula serializer formula) := by
  simp [formula, renameFormula, renameTerm, historical_collision, Holds, allBound, evaluate,
    integerTarget, CoreFormula.evalRelation, FullSyntax.update]

/-- Encoding names before lowering to solver symbols preserves the counterexample. -/
theorem encoded_false (env : FullSyntax.Name → Int) :
    ¬Holds integerTarget env (renameFormula encode formula) := by
  rw [formula_meaning integerTarget encode (fun _ _ equal => encode_injective equal)]
  exact original_false _

/-- Complete repaired serialization also preserves the original false meaning. -/
theorem repaired_false (env : FullSyntax.Name → Int) :
    ¬Holds integerTarget env (renameFormula (serializer ∘ encode) formula) := by
  rw [formula_meaning integerTarget (serializer ∘ encode) (fun _ _ equal => serialized_injective equal)]
  exact original_false _

/-- The actual entailment assertion asks for a counterexample to the universal equality. -/
def request : Prepared := ⟨declarations [("1", .int)], assertion [] .top sourceFormula⟩

/-- The source preflight produces this request, including the default value declaration. -/
theorem prepared : prepareQuery [("1", .int)] [] [] .top sourceFormula = some request := by
  simp [prepareQuery, prepare, freshDeclarations, mentioned, lowerFormula, lowerTerm, lowerSort,
    sourceFormula, formulaSymbols, termSymbols, partsSymbols, lowerParts, undeclared, declarations,
    valueName, request]

/-- The prepared assertion retains the exact counterexample formula. -/
theorem request_asserted : request.asserted = .and [.true, .not formula] := by
  simp [request, assertion, lowerParts, lowerFormula, lowerTerm, lowerSort, sourceFormula, formula]

/-- The original counterexample assertion is satisfiable in the declared integer domain. -/
theorem original_sat : ResponseCorrect integerTarget request .sat := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp [request, declarations, valueName, Admitted, integerTarget]
  · rw [request_asserted]
    simpa only [Holds, holdsAll, true_and, and_true] using original_false (fun _ => 0)

/-- The source query is not valid even though its declared name is an integer. -/
theorem original_not_entails : ¬Entails integerTarget request.declared [] .top sourceFormula := by
  intro entailed
  exact (unsat_iff_entails integerTarget request.declared [] .top sourceFormula).mpr entailed original_sat

/-- The old serializer makes the submitted counterexample assertion unsatisfiable. -/
theorem historical_unsat : ResponseCorrect integerTarget (renamePrepared serializer request) .unsat := by
  rintro ⟨env, _, assumed⟩
  have denied : ¬Holds integerTarget env (renameFormula serializer formula) := by
    change Holds integerTarget env (renameFormula serializer request.asserted) at assumed
    rw [request_asserted] at assumed
    simpa only [renameFormula, renameParts, Holds, holdsAll, true_and, and_true] using assumed
  exact denied (historical_true env)

/-- A correct response to the old submitted assertion maps to an unsound source Yes. -/
theorem historical_yes_unsound (milliseconds : Int) (reached : Bool) :
    ResponseCorrect integerTarget (renamePrepared serializer request) .unsat ∧
      responseVerdict milliseconds reached .unsat = .returned .yes ∧
      ¬Guards.Supports .yes (Entails integerTarget request.declared [] .top sourceFormula) :=
  ⟨historical_unsat, rfl, original_not_entails⟩

/-- The repaired assertion has a counterexample after full serialization. -/
theorem repaired_sat : ResponseCorrect integerTarget (renamePrepared (serializer ∘ encode) request) .sat := by
  exact (satisfiable_rename integerTarget (serializer ∘ encode)
    (fun _ _ equal => serialized_injective equal) request).mpr original_sat

/-- A correct Sat response to the repaired assertion maps to the intended source No. -/
theorem repaired_no_supported (milliseconds : Int) (reached : Bool) :
    ResponseCorrect integerTarget (renamePrepared (serializer ∘ encode) request) .sat ∧
      responseVerdict milliseconds reached .sat = .returned .no ∧
      Guards.Supports .no (Entails integerTarget request.declared [] .top sourceFormula) :=
  ⟨repaired_sat, rfl, original_not_entails⟩

end MicroCFTA.SourceSolverNameCollision
