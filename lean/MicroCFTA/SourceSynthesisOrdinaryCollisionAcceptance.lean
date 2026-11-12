import MicroCFTA.SourceSynthesisOrdinaryTypeCollision
import MicroCFTA.SourceSynthesisFirstOrderTotality

/-!
# Actual source acceptance of the reserved raw type collision

The existing literal query gives f a rigid variable domain and x the distinct
raw constant var1. Their source annotations coincide. Actual required-query
rows accept the application even though it has no independent ordinary type.

This is a source constructor counterexample. It assumes no successful output
or acceptance supplier and makes no new Haskell execution claim.
-/
namespace MicroCFTA.SourceSynthesisOrdinaryCollisionAcceptance
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisOrdinaryTypeCollision (emptyLibrary badQuery badQuery_untypable)
open SourceSynthesisTypeEncodingCollision (reserved_variable_constant_collision)
open SourceSynthesisSourceTermsTyping (RelevantTyping)
open SourceSynthesisSelections (resolveSelection selections_two lookupLast self_mem_permutations)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

private abbrev functionRow : Row :=
  .mk "f" top [typeNode top (.tFun (.tVar "a") (.tCons "B" []))]

private abbrev argumentRow : Row :=
  .mk "x" top [typeNode top (.tCons "var1" [])]

private def functionTerm : Term Symbol :=
  .node (literal "f") [.node (literal "->")
    [marker, rigidTerm (.tVar "a"), rigidTerm (.tCons "B" [])]]

private def argumentTerm : Term Symbol :=
  .node (literal "x") [rigidTerm (.tCons "var1" [])]

/-- The literal body applies f to x with their actual colliding source annotations. -/
def collisionBody : Term Symbol :=
  .node (literal "app") [rigidTerm (.tCons "B" []), marker, functionTerm, argumentTerm]

/-- The literal root retains the existing query goal and the collision body. -/
def collisionWitness : Term Symbol :=
  .node (literal "filter") [rigidTerm badQuery.queryGoal, collisionBody]

private theorem argument_edges :
    (context emptyLibrary badQuery).argumentEdges = [("f", functionRow), ("x", argumentRow)] := rfl

private theorem resolve_pair :
    resolveArguments (context emptyLibrary badQuery) ["f", "x"] =
      some [("f", functionRow), ("x", argumentRow)] := by
  rw [resolveArguments, argument_edges]
  simp [resolveSelection, selections_two, lookupLast]

private theorem resolve_function :
    resolveArguments (context emptyLibrary badQuery) ["f"] = some [("f", functionRow)] := by
  rw [resolveArguments, argument_edges]
  simp [resolveSelection, selections_two, lookupLast]

private theorem resolve_argument :
    resolveArguments (context emptyLibrary badQuery) ["x"] = some [("x", argumentRow)] := by
  rw [resolveArguments, argument_edges]
  simp [resolveSelection, selections_two, lookupLast]

private theorem result_in :
    TypeIn (constructorCatalog emptyLibrary badQuery) (rigidTerm (.tCons "B" [])) := by
  have present : ("B", 0) ∈ constructorCatalog emptyLibrary badQuery := by
    simp [constructorCatalog, List.mem_eraseDups, badQuery, constructorsOf]
  have finite := TypeIn.node (catalog := constructorCatalog emptyLibrary badQuery) "B" []
    present (fun child member => nomatch member)
  simpa only [rigidTerm, List.map_nil] using finite

private theorem source_body :
    RelevantTyping emptyLibrary badQuery true 2 ["f", "x"] (.app (.var "f") (.var "x"))
      (rigidTerm badQuery.queryGoal) collisionBody := by
  have function : RelevantTyping emptyLibrary badQuery false 1 ["f"] (.var "f")
      (.node (literal "->") [marker, rigidTerm (.tVar "a"), rigidTerm (.tCons "B" [])])
      functionTerm := by
    simpa only [functionTerm, rigidTerm] using
      (RelevantTyping.singleton (lib := emptyLibrary) (query := badQuery) (asArgument := false)
        "f" (.tFun (.tVar "a") (.tCons "B" [])) resolve_function)
  have argument : RelevantTyping emptyLibrary badQuery true 1 ["x"] (.var "x")
      (rigidTerm (.tVar "a")) argumentTerm := by
    have single := RelevantTyping.singleton (lib := emptyLibrary) (query := badQuery) (asArgument := true)
      "x" (.tCons "var1" []) resolve_argument
    have encoded := reserved_variable_constant_collision.2.1
    simpa only [argumentTerm, ← encoded] using single
  have built : RelevantTyping emptyLibrary badQuery true 2 ["f", "x"]
      (.app (.var "f") (.var "x")) (rigidTerm (.tCons "B" []))
      (.node (literal "app") [rigidTerm (.tCons "B" []), marker, functionTerm, argumentTerm]) :=
    .split (left := 1) (offset := 1) (arguments := [("f", functionRow), ("x", argumentRow)])
      resolve_pair (by simp) (by decide) (by decide) (by decide) (by decide)
      function argument result_in
  exact built

/-- Actual source acceptance and decoding coexist with failure of ordinary typing at every raw type. -/
theorem source_accepts_untypable [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ expression, firstOrderRaw emptyLibrary badQuery 2 = .ok expression ∧
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression)
        collisionWitness ∧
      Projection literal Prod.fst collisionWitness (.app (.var "f") (.var "x")) ∧
      toProgram literal Prod.fst collisionWitness = .app (.var "f") (.var "x") ∧
      (toProgram literal Prod.fst collisionWitness).components = 2 ∧
      ∀ typ, ¬Typed emptyLibrary badQuery (.app (.var "f") (.var "x")) typ := by
  have sourceAtRoot : RelevantTyping emptyLibrary badQuery true (2 : Int).toNat
      ((context emptyLibrary badQuery).argumentEdges.map Prod.fst)
      (.app (.var "f") (.var "x")) (rigidTerm badQuery.queryGoal) collisionBody := source_body
  obtain ⟨expression, returned, accepted, projected, _count⟩ :=
    SourceSynthesisFirstOrderTotality.firstOrderRaw_member_total formulas solver 2 (by decide)
      (context emptyLibrary badQuery).argumentEdges (self_mem_permutations _)
      (.app (.var "f") (.var "x")) collisionBody sourceAtRoot
  have projectedWitness : Projection literal Prod.fst collisionWitness (.app (.var "f") (.var "x")) :=
    projected
  have decoded := projectedWitness.toProgram_eq
  exact ⟨expression, returned, accepted, projectedWitness, decoded,
    (congrArg Program.components decoded).trans rfl, badQuery_untypable⟩

end MicroCFTA.SourceSynthesisOrdinaryCollisionAcceptance
