import MicroCFTA.SourceSynthesisOrdinaryTyping
import MicroCFTA.SourceSynthesisTypeEncodingCollision

/-!
# No ordinary type for the reserved-name application

The query gives f a rigid variable domain. It gives x a distinct raw
constructor type. Their native annotations coincide, but ordinary typing
cannot apply f to x. Conversion under the documented Fun/2 alias does not
change that result. These laws use no generator admission premise.
-/
namespace MicroCFTA.SourceSynthesisOrdinaryTypeCollision
open SourceSynthesisTypeSyntax
open SourceSynthesisProgramTermSize (Program)
open SourceSynthesisOrdinaryTyping
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
open SourceSynthesisTypeEncodingCollision (reserved_variable_constant_collision)

/-- The counterexample has no component or argument-only binding. -/
def emptyLibrary : Library :=
  { libraryGroups := []
    libraryArgumentOnly := []
    libraryAvoid := []
    libraryEncoding := .firstOrder }

/-- The literal query keeps a variable domain and a distinct constructor argument. -/
def badQuery : Query :=
  { queryArguments :=
      [("f", .tFun (.tVar "a") (.tCons "B" [])), ("x", .tCons "var1" [])]
    queryGoal := .tCons "B" [] }

private theorem lookup_function :
    queryLookup badQuery.queryArguments "f" = some (.tFun (.tVar "a") (.tCons "B" [])) := by
  simp [queryLookup, badQuery, List.lookup]

private theorem lookup_argument :
    queryLookup badQuery.queryArguments "x" = some (.tCons "var1" []) := by
  simp [queryLookup, badQuery]

private theorem variable_origin {program : Program} {typ : Ty}
    (typed : Typed emptyLibrary badQuery program typ) :
    ∀ name, program = .var name →
      ∃ original, queryLookup badQuery.queryArguments name = some original ∧ Equivalent original typ := by
  induction typed with
  | group entry binding rho => cases binding
  | argumentOnly entry binding rho => cases binding
  | queryArgument found =>
      intro name shape
      cases shape
      exact ⟨_, found, rfl⟩
  | application first second _firstIH _secondIH =>
      intro name shape
      cases shape
  | conversion typed same ih =>
      intro name shape
      obtain ⟨original, found, equivalent⟩ := ih name shape
      exact ⟨original, found, Eq.trans equivalent same⟩

private theorem no_bad_application {program : Program} {typ : Ty}
    (typed : Typed emptyLibrary badQuery program typ) :
    program = .app (.var "f") (.var "x") → False := by
  induction typed with
  | group entry binding rho => cases binding
  | argumentOnly entry binding rho => cases binding
  | queryArgument found =>
      intro shape
      cases shape
  | @application function argument domain codomain first second _firstIH _secondIH =>
      intro shape
      have children := Program.app.inj shape
      obtain ⟨functionType, functionFound, functionEquivalent⟩ := variable_origin first "f" children.1
      obtain ⟨argumentType, argumentFound, argumentEquivalent⟩ := variable_origin second "x" children.2
      have functionSame := Option.some.inj (lookup_function.symm.trans functionFound)
      have argumentSame := Option.some.inj (lookup_argument.symm.trans argumentFound)
      rw [← functionSame] at functionEquivalent
      rw [← argumentSame] at argumentEquivalent
      change normalizeTy (.tFun (.tVar "a") (.tCons "B" [])) =
        normalizeTy (.tFun domain codomain) at functionEquivalent
      simp only [normalizeTy, List.map_nil] at functionEquivalent
      have functionDomain : Ty.tVar "a" = normalizeTy domain := (Ty.tFun.inj functionEquivalent).1
      have argumentDomain : Ty.tCons "var1" [] = normalizeTy domain := by
        simpa only [Equivalent, normalizeTy, List.map_nil] using argumentEquivalent
      exact reserved_variable_constant_collision.1 (functionDomain.trans argumentDomain.symm)
  | conversion _typed _same ih => exact ih

/-- The reproduced application has no ordinary type under its literal query bindings. -/
theorem badQuery_untypable (typ : Ty) :
    ¬Typed emptyLibrary badQuery (.app (.var "f") (.var "x")) typ := by
  intro typed
  exact no_bad_application typed rfl

/-- Native type equality coexists with failure of independent ordinary typing. -/
theorem same_annotation_but_no_ordinary_type (typ : Ty) :
    rigidTerm (.tVar "a") = rigidTerm (.tCons "var1" []) ∧
      ¬Typed emptyLibrary badQuery (.app (.var "f") (.var "x")) typ :=
  ⟨reserved_variable_constant_collision.2.1, badQuery_untypable typ⟩

end MicroCFTA.SourceSynthesisOrdinaryTypeCollision
