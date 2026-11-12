import MicroCFTA.SourceSynthesisOrdinaryTypeCollision

/-!
# Ordinary Fun/0 typing and the source universe boundary

The raw syntax admits a non-arrow Fun constructor. The actual constructor
catalog omits it. An ordinary application can have that result type while
its result annotation has no structural TypeIn witness. The separate Haskell
packet checks actual rejection. This file does not infer nonmembership from
failure of a sufficient structural witness.
-/
namespace MicroCFTA.SourceSynthesisFunArityBoundary
open Language
open SourceSynthesisTypeSyntax
open SourceSynthesisFirstOrderConstruction (constructorCatalog)
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisOrdinaryTyping
open SourceSynthesisOrdinaryTypeCollision (emptyLibrary)
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- The query uses an ordinary nullary Fun constructor as its result. -/
def funZeroQuery : Query :=
  { queryArguments :=
      [("f", .tFun (.tCons "A" []) (.tCons "Fun" [])), ("x", .tCons "A" [])]
    queryGoal := .tCons "Fun" [] }

/-- The actual source discovers A but omits the nullary Fun constructor. -/
theorem fun_zero_catalog : constructorCatalog emptyLibrary funZeroQuery = [("A", 0)] := by
  simp [constructorCatalog, emptyLibrary, funZeroQuery, constructorsOf]
  decide

/-- The omitted result has no structural witness in that actual catalog. -/
theorem fun_zero_no_type_in :
    ¬ TypeIn (constructorCatalog emptyLibrary funZeroQuery) (rigidTerm (.tCons "Fun" [])) := by
  have literalResult : rigidTerm (.tCons "Fun" []) = .node (literal "Fun") [] := by
    simp [rigidTerm]
  rw [literalResult]
  intro witness
  generalize term : (Term.node (literal "Fun") [] : Term _) = observed at witness
  cases witness <;> simp_all [SourceSynthesisLabelProgramBuildRoles.literal, fun_zero_catalog]
  rename_i name present
  subst name
  simp_all

/-- The same query has an ordinary application with the omitted result type. -/
theorem fun_zero_application_ordinary :
    Typed emptyLibrary funZeroQuery (.app (.var "f") (.var "x")) (.tCons "Fun" []) := by
  apply Typed.application (domain := .tCons "A" [])
  · apply Typed.queryArgument
    simp [queryLookup, funZeroQuery, List.lookup]
  · apply Typed.queryArgument
    simp [queryLookup, funZeroQuery]

end MicroCFTA.SourceSynthesisFunArityBoundary
