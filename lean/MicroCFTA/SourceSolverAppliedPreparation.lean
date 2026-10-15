import MicroCFTA.SourceAppliedDeclarations

/-!
# Current source preflight with inferred applied-name sorts

The reserved-name checks and assertion retain their existing definitions.
Only undeclared applied names receive new function sorts. Encoding preserves
the complete preparation, including last-occurrence arity selection.
-/
namespace MicroCFTA.SourceSolverAppliedPreparation
open FullSyntax (Name)
open FormulaLowering SolverAdapter SourceSizedLiquidProgram SourceSolverNameSemantics
open SourceSolverNamePreparation

/-- Current source preparation before the common injective name encoding. -/
def prepare (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) : Option Prepared := do
  let ambient := declarations given
  let fresh ← SourceSizedLiquidAmbientRepair.reservedFreshList ambient assumptions query.bindings
  pure ⟨ambient ++ fresh ++ SourceAppliedDeclarations.undeclared ambient fresh
    (mentioned assumptions query.antecedent query.consequent)
    (SourceAppliedDeclarations.queryApplications assumptions query.antecedent query.consequent),
    assertion assumptions query.antecedent query.consequent⟩

/-- Actual source arity keys pass through nameSymbol after source-order collection. -/
def prepareRenamed (rename : Name → Name) (given : List Declaration)
    (assumptions : List FullSyntax.Formula) (query : Query) : Option Prepared := do
  let ambient := encodedDeclarations rename given
  let fresh ← reservedFreshListAt ambient (renameParts rename (lowerParts assumptions))
    (query.bindings.map (mapBinding rename))
  pure ⟨ambient ++ fresh ++ SourceAppliedDeclarations.undeclared ambient fresh
    (encodedMentioned rename assumptions query.antecedent query.consequent)
    ((SourceAppliedDeclarations.queryApplications assumptions query.antecedent query.consequent).map
      fun entry => (rename entry.1, entry.2)),
    encodedAssertion rename assumptions query.antecedent query.consequent⟩

/-- Every source operation commutes with the actual injective name encoding. -/
theorem prepare_rename (rename : Name → Name) (injective : Function.Injective rename)
    (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) :
    prepareRenamed rename given assumptions query = (prepare given assumptions query).map (renamePrepared rename) := by
  simp only [prepareRenamed, declarations_rename rename injective,
    reservedFreshList_rename rename injective, prepare]
  cases SourceSizedLiquidAmbientRepair.reservedFreshList (declarations given) assumptions query.bindings with
  | none => rfl
  | some fresh =>
      simp only [Option.map_some, bind, Option.bind, pure, Option.some.injEq]
      simp only [mentioned_rename rename injective, SourceAppliedDeclarations.undeclared_rename rename injective,
        assertion_rename, renamePrepared, List.map_append]
      rfl

/-- The current native preflight uses the established two-form name codec. -/
def encodedPrepare (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) : Option Prepared :=
  prepareRenamed SourceSolverNameFastEncoding.encode given assumptions query

/-- Full current preparation preserves declarations and assertion under native name encoding. -/
theorem sourcePrepare_encode (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) :
    encodedPrepare given assumptions query = (prepare given assumptions query).map
      (renamePrepared SourceSolverNameFastEncoding.encode) :=
  prepare_rename _ (fun _ _ same => SourceSolverNameFastEncoding.encode_injective same) given assumptions query

/-- Applied-name sort inference does not change the source reserved-name rejection cases. -/
theorem rejected (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) :
    prepare given assumptions query = none ↔ SourceSizedLiquidAmbientRepair.sourcePrepare given assumptions query = none := by
  unfold prepare SourceSizedLiquidAmbientRepair.sourcePrepare
  cases SourceSizedLiquidAmbientRepair.reservedFreshList (declarations given) assumptions query.bindings <;> simp

/-- Queries without applications retain the entire historical prepared request. -/
theorem app_free (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query)
    (clear : SourceAppliedDeclarations.queryApplications assumptions query.antecedent query.consequent = []) :
    prepare given assumptions query = SourceSizedLiquidAmbientRepair.sourcePrepare given assumptions query := by
  simp only [prepare, clear, SourceAppliedDeclarations.undeclared_empty, SourceSizedLiquidAmbientRepair.sourcePrepare]

/-- Application-free requests also retain the complete historical encoded request. -/
theorem encoded_app_free (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query)
    (clear : SourceAppliedDeclarations.queryApplications assumptions query.antecedent query.consequent = []) :
    encodedPrepare given assumptions query = SourceSolverNamePreparation.encodedPrepare given assumptions query := by
  rw [sourcePrepare_encode, app_free given assumptions query clear,
    SourceSolverNamePreparation.encodedPrepare,
    SourceSolverNamePreparation.sourcePrepare_rename _ (fun _ _ same => SourceSolverNameFastEncoding.encode_injective same)]

/-- Embedded arithmetic-core queries and assumptions retain the existing complete adapter. -/
theorem core (given : List Declaration) (bindings : List (Name × Name)) (assumptions : List CoreFormula.Formula)
    (antecedent consequent : CoreFormula.Formula) :
    prepare given (FullSyntax.embedParts assumptions)
        ⟨bindings, FullSyntax.embedFormula antecedent, FullSyntax.embedFormula consequent⟩ =
      SourceSizedLiquidAmbientRepair.sourcePrepare given (FullSyntax.embedParts assumptions)
        ⟨bindings, FullSyntax.embedFormula antecedent, FullSyntax.embedFormula consequent⟩ := by
  apply app_free
  simp only [SourceAppliedDeclarations.queryApplications, SourceAppliedDeclarations.core_formula,
    SourceAppliedDeclarations.core_parts, List.nil_append]

end MicroCFTA.SourceSolverAppliedPreparation
