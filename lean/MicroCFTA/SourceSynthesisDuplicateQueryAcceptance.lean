import MicroCFTA.SourceSynthesisOrdinaryTyping
import MicroCFTA.SourceSynthesisFirstOrderTotality

/-!
# Duplicate query rows and ordinary last lookup

An unrestricted source leaf can use an earlier query row. Required singleton
calls resolve the same name to the later row. The concrete four-component
Program uses both behaviors, while ordinary typing always reads the later
binding. The type names A, C, and R use no reserved encoding tags.

This law concerns the actual source constructor. It makes no Haskell runtime
claim and introduces no restriction on the public Query input.
-/
namespace MicroCFTA.SourceSynthesisDuplicateQueryAcceptance
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (top variables occurrences isVariableSymbol)
open SourceSynthesisGeneralizeFiniteInstances (instantiate)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisSourceTermsTyping
  (LeafTyping TermsTyping RelevantTyping fallbackFunctionRows)
open SourceSynthesisOrdinaryTyping
  (Typed Equivalent normalizeTy queryLookup queryLookup_member)
open SourceSynthesisTypeSubstitutionWitnesses (substTy query_argument_terms)
open SourceSynthesisSelections
  (resolveSelection resolveSelection_empty duplicate_singleton duplicate_pair self_mem_permutations)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

private abbrev aTy : Ty := .tCons "A" []
private abbrev cTy : Ty := .tCons "C" []
private abbrev rTy : Ty := .tCons "R" []
private abbrev secondTy : Ty := .tFun cTy rTy
private abbrev firstTy : Ty := .tFun cTy secondTy
private abbrev gTy : Ty := .tFun aTy firstTy

/-- The sole monomorphic component expects A followed by two C arguments. -/
def library : Library :=
  { libraryGroups := [("g", gTy, ["g"])]
    libraryArgumentOnly := []
    libraryAvoid := []
    libraryEncoding := .firstOrder }

/-- Both original query entries remain present under the same name. -/
def query : Query :=
  { queryArguments := [("x", aTy), ("x", cTy)]
    queryGoal := rTy }

/-- The literal Program applies g to three occurrences of x. -/
def program : Program :=
  .app (.app (.app (.var "g") (.var "x")) (.var "x")) (.var "x")

private abbrev gRow : Row := component (context library query).types "g" gTy
private abbrev rowA : Row := .mk "x" top [typeNode top aTy]
private abbrev rowC : Row := .mk "x" top [typeNode top cTy]

private def gTerm : Term Symbol := .node (literal "g") [rigidTerm gTy]
private def earlierTerm : Term Symbol := .node (literal "x") [rigidTerm aTy]
private def laterTerm : Term Symbol := .node (literal "x") [rigidTerm cTy]
private def firstBody : Term Symbol :=
  .node (literal "app") [rigidTerm firstTy, marker, gTerm, earlierTerm]
private def secondBody : Term Symbol :=
  .node (literal "app") [rigidTerm secondTy, marker, firstBody, laterTerm]

/-- The source body uses the earlier A row once and the later C row twice. -/
def duplicateBody : Term Symbol :=
  .node (literal "app") [rigidTerm rTy, marker, secondBody, laterTerm]

/-- The actual filter root retains the query goal R and the same body. -/
def duplicateWitness : Term Symbol :=
  .node (literal "filter") [rigidTerm query.queryGoal, duplicateBody]

private theorem resolve_empty : resolveArguments (context library query) [] = some [] :=
  resolveSelection_empty _

private theorem resolve_single :
    resolveArguments (context library query) ["x"] = some [("x", rowC)] := by
  change resolveSelection [("x", rowA), ("x", rowC)] ["x"] = some [("x", rowC)]
  exact duplicate_singleton "x" rowA rowC

private theorem resolve_pair :
    resolveArguments (context library query) ["x", "x"] = some [("x", rowC), ("x", rowA)] := by
  change resolveSelection [("x", rowA), ("x", rowC)] ["x", "x"] =
    some [("x", rowC), ("x", rowA)]
  exact duplicate_pair "x" rowA rowC

private theorem constant_in (name : String)
    (present : (name, 0) ∈ constructorCatalog library query) :
    TypeIn (constructorCatalog library query) (rigidTerm (.tCons name [])) := by
  have finite := TypeIn.node (catalog := constructorCatalog library query) name []
    present (fun _child member => nomatch member)
  simpa only [rigidTerm, List.map_nil] using finite

private theorem c_in : TypeIn (constructorCatalog library query) (rigidTerm cTy) := by
  apply constant_in "C"
  simp [constructorCatalog, List.mem_eraseDups, query, constructorsOf]

private theorem r_in : TypeIn (constructorCatalog library query) (rigidTerm rTy) := by
  apply constant_in "R"
  simp [constructorCatalog, List.mem_eraseDups, query, constructorsOf]

private theorem second_in : TypeIn (constructorCatalog library query) (rigidTerm secondTy) := by
  simpa only [rigidTerm] using TypeIn.arrow (rigidTerm cTy) (rigidTerm rTy) c_in r_in

private theorem first_in : TypeIn (constructorCatalog library query) (rigidTerm firstTy) := by
  simpa only [rigidTerm] using TypeIn.arrow (rigidTerm cTy) (rigidTerm secondTy) c_in second_in

private theorem g_leaf :
    LeafTyping (constructorCatalog library query) gRow (.var "g") (rigidTerm gTy) gTerm := by
  have typed := LeafTyping.component (catalog := constructorCatalog library query) "g" gTy
    (fun _key => rigidTerm rTy) (by
      intro key member
      simp [variables, occurrences, SourceSynthesisGeneralizeSyntax.shift, isVariableSymbol] at member)
  have safe : SourceSynthesisTypeSubstitutionWitnesses.AliasSafe gTy := by
    simp [SourceSynthesisTypeSubstitutionWitnesses.AliasSafe, isVariableSymbol]
  have compatible := SourceSynthesisTypeSubstitutionWitnesses.instantiate_rigid_of_compatible
    gTy (fun _name => rTy) (fun _key => rigidTerm rTy) safe (fun _name _member => rfl)
  have monomorphic : substTy (fun _name => rTy) gTy = gTy := by simp [substTy]
  rw [monomorphic] at compatible
  rw [compatible] at typed
  have rowSame : component (allTypes top (constructorCatalog library query)) "g" gTy = gRow := rfl
  rw [rowSame] at typed
  exact typed

private theorem first_terms :
    TermsTyping library query false 2 (.app (.var "g") (.var "x"))
      (rigidTerm firstTy) firstBody := by
  have selected : gRow ∈ fallbackFunctionRows (context library query) := by
    change gRow ∈ [gRow, rowA, rowC]
    exact List.mem_cons_self
  have function : LeafTyping (constructorCatalog library query) gRow (.var "g")
      (.node (literal "->") [marker, rigidTerm aTy, rigidTerm firstTy]) gTerm := by
    simpa only [rigidTerm] using g_leaf
  have argument : TermsTyping library query true 1 (.var "x") (rigidTerm aTy) earlierTerm :=
    query_argument_terms library query true ("x", aTy) List.mem_cons_self
  exact .fallback selected function argument first_in

private theorem marked_x :
    RelevantTyping library query true 1 ["x"] (.var "x") (rigidTerm cTy) laterTerm :=
  .singleton "x" cTy resolve_single

private theorem second_relevant :
    RelevantTyping library query false 3 ["x"]
      (.app (.app (.var "g") (.var "x")) (.var "x")) (rigidTerm secondTy) secondBody := by
  have initial : RelevantTyping library query false 2 [] (.app (.var "g") (.var "x"))
      (rigidTerm firstTy) firstBody := .empty resolve_empty first_terms
  have function : RelevantTyping library query false 2 [] (.app (.var "g") (.var "x"))
      (.node (literal "->") [marker, rigidTerm cTy, rigidTerm secondTy]) firstBody := by
    simpa only [rigidTerm] using initial
  exact .split (left := 2) (offset := 0) (arguments := [("x", rowC)]) resolve_single
    (by simp) (by decide) (by decide) (by decide) (by decide) function marked_x second_in

private theorem source_body :
    RelevantTyping library query true 4 ["x", "x"] program (rigidTerm query.queryGoal) duplicateBody := by
  have function : RelevantTyping library query false 3 ["x"]
      (.app (.app (.var "g") (.var "x")) (.var "x"))
      (.node (literal "->") [marker, rigidTerm cTy, rigidTerm rTy]) secondBody := by
    simpa only [rigidTerm] using second_relevant
  exact .split (left := 3) (offset := 1) (arguments := [("x", rowC), ("x", rowA)]) resolve_pair
    (by simp) (by decide) (by decide) (by decide) (by decide) function marked_x r_in

private theorem lookup_x : queryLookup query.queryArguments "x" = some cTy := by
  simp [queryLookup, query]

private theorem variable_origin {value : Program} {typ : Ty}
    (typed : Typed library query value typ) :
    ∀ name, value = .var name →
      (name = "g" ∧ Equivalent gTy typ) ∨ (name = "x" ∧ Equivalent cTy typ) := by
  induction typed with
  | group entry binding _rho =>
      change entry ∈ [("g", gTy, ["g"])] at binding
      have selected := List.mem_singleton.mp binding
      subst entry
      intro name shape
      have named := Program.var.inj shape
      refine .inl ⟨named.symm, ?_⟩
      simp [Equivalent, normalizeTy, substTy]
  | argumentOnly _entry binding _rho =>
      change _ ∈ ([] : List (String × Ty)) at binding
      cases binding
  | @queryArgument selected result found =>
      have member := queryLookup_member query.queryArguments selected result found
      change (selected, result) ∈ [("x", aTy), ("x", cTy)] at member
      have selectedSame : selected = "x" := by
        rcases List.mem_cons.mp member with same | member
        · exact (Prod.mk.inj same).1
        · exact (Prod.mk.inj (List.mem_singleton.mp member)).1
      subst selected
      have resultSame := Option.some.inj (lookup_x.symm.trans found)
      subst result
      intro name shape
      have named := Program.var.inj shape
      exact .inr ⟨named.symm, rfl⟩
  | application _first _second _firstIH _secondIH =>
      intro _name shape
      cases shape
  | conversion _typed same ih =>
      intro name shape
      rcases ih name shape with ⟨named, original⟩ | ⟨named, original⟩
      · exact .inl ⟨named, Eq.trans original same⟩
      · exact .inr ⟨named, Eq.trans original same⟩

private theorem no_first_application {value : Program} {typ : Ty}
    (typed : Typed library query value typ) :
    value = .app (.var "g") (.var "x") → False := by
  induction typed with
  | group _entry _binding _rho => intro shape; cases shape
  | argumentOnly _entry _binding _rho => intro shape; cases shape
  | queryArgument _found => intro shape; cases shape
  | @application _function _argument domain codomain first second _firstIH _secondIH =>
      intro shape
      have children := Program.app.inj shape
      have functionEquivalent : Equivalent gTy (.tFun domain codomain) := by
        rcases variable_origin first "g" children.1 with ⟨_named, same⟩ | ⟨wrong, _same⟩
        · exact same
        · simp at wrong
      have argumentEquivalent : Equivalent cTy domain := by
        rcases variable_origin second "x" children.2 with ⟨wrong, _same⟩ | ⟨_named, same⟩
        · simp at wrong
        · exact same
      change normalizeTy gTy = normalizeTy (.tFun domain codomain) at functionEquivalent
      simp only [normalizeTy, List.map_nil] at functionEquivalent
      have functionDomain : aTy = normalizeTy domain := (Ty.tFun.inj functionEquivalent).1
      have argumentDomain : cTy = normalizeTy domain := by
        simpa only [Equivalent, normalizeTy, List.map_nil] using argumentEquivalent
      have impossible : aTy = cTy := functionDomain.trans argumentDomain.symm
      simp at impossible
  | conversion _typed _same ih => exact ih

private theorem application_function {value : Program} {typ : Ty}
    (typed : Typed library query value typ) :
    ∀ function argument, value = .app function argument →
      ∃ domain codomain, Typed library query function (.tFun domain codomain) := by
  induction typed with
  | group _entry _binding _rho => intro _function _argument shape; cases shape
  | argumentOnly _entry _binding _rho => intro _function _argument shape; cases shape
  | queryArgument _found => intro _function _argument shape; cases shape
  | @application _function _argument domain codomain first _second _firstIH _secondIH =>
      intro function _argument shape
      have same := (Program.app.inj shape).1
      exact ⟨domain, codomain, same ▸ first⟩
  | conversion _typed _same ih => exact ih

private theorem program_untypable (typ : Ty) : ¬Typed library query program typ := by
  intro typed
  obtain ⟨_domain, _codomain, second⟩ := application_function typed
    (.app (.app (.var "g") (.var "x")) (.var "x")) (.var "x") rfl
  obtain ⟨_domain, _codomain, first⟩ := application_function second
    (.app (.var "g") (.var "x")) (.var "x") rfl
  exact no_first_application first rfl

/-- Actual source acceptance and exact decoding coexist with ordinary untypability at every raw type. -/
theorem duplicate_query_source_counterexample [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ expression, firstOrderRaw library query 4 = .ok expression ∧
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression)
        duplicateWitness ∧
      Projection literal Prod.fst duplicateWitness program ∧
      toProgram literal Prod.fst duplicateWitness = program ∧
      (toProgram literal Prod.fst duplicateWitness).components = 4 ∧
      ∀ typ, ¬Typed library query program typ := by
  have sourceAtRoot : RelevantTyping library query true (4 : Int).toNat
      ((context library query).argumentEdges.map Prod.fst) program
      (rigidTerm query.queryGoal) duplicateBody := source_body
  obtain ⟨expression, returned, accepted, projected, _count⟩ :=
    SourceSynthesisFirstOrderTotality.firstOrderRaw_member_total formulas solver 4 (by decide)
      (context library query).argumentEdges (self_mem_permutations _) program duplicateBody sourceAtRoot
  have projectedWitness : Projection literal Prod.fst duplicateWitness program := projected
  have decoded := projectedWitness.toProgram_eq
  exact ⟨expression, returned, accepted, projectedWitness, decoded,
    (congrArg Program.components decoded).trans rfl, program_untypable⟩

end MicroCFTA.SourceSynthesisDuplicateQueryAcceptance
