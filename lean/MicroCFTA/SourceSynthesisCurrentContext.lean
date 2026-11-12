import MicroCFTA.SourceSynthesisPr210TypeReflection
import MicroCFTA.SourceSynthesisPr211QueryBindings
import MicroCFTA.SourceSynthesisAnnotatedProgramWitnesses

/-!
# Current FirstOrder synthesis context

This syntax follows merged main e538 after PR210 and PR211. Constructor
names use the checked encoding. Only Fun with two arguments is an arrow
alias. Query rows and constructor discovery use the same last-binding rule.
The historical context and source constructor remain unchanged.

The laws give current query-leaf membership and projection. They do not
establish native execution, refinement lookup, or whole Program acceptance.
The existing Context and row evaluators are reused without a second engine.
-/
namespace MicroCFTA.SourceSynthesisCurrentContext
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax (Ty Library Query allTypes)
open SourceSynthesisGeneralizeSyntax (Guard top isVariableSymbol)
open SourceSynthesisFirstOrderConstruction (Expression Row Context component termsRows)
open SourceSynthesisPr210ConstructorEscape (escapeConstructor escapeConstructor_separate)
open SourceSynthesisPr210TypeReflection (encodeTy candidateRigid)
open SourceSynthesisPr211QueryBindings (queryBindings queryBindings_names
  queryBindings_length queryBindings_lookup)
open SourceSynthesisOrdinaryTyping (Typed queryLookup queryLookup_member)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapEdges mapEdges_eq_map)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- Encode the current rigid type through the historical instruction constructor. -/
def typeNode (typ : Ty) : Expression := SourceSynthesisTypeSyntax.typeNode top (encodeTy typ)

/-- Discover escaped constructors and exclude only the two-argument Fun alias. -/
def constructorsOf : Ty → List (String × Nat)
  | .tVar _ => []
  | .tFun argument result => constructorsOf argument ++ constructorsOf result
  | .tCons name children =>
      (if name = "Fun" ∧ children.length = 2 then []
       else [(escapeConstructor name, children.length)]) ++ children.flatMap constructorsOf

/-- Discover the current catalog in source order from canonical query bindings. -/
def constructorCatalog (lib : Library) (query : Query) : List (String × Nat) :=
  (lib.libraryGroups.flatMap (fun entry => constructorsOf entry.2.1) ++
    lib.libraryArgumentOnly.flatMap (fun entry => constructorsOf entry.2) ++
    (queryBindings query).flatMap (fun entry => constructorsOf entry.2) ++
    constructorsOf query.queryGoal).eraseDups

/-- Build the current FirstOrder fields in the existing source context. -/
def context (lib : Library) (query : Query) : Context :=
  let types := allTypes top (constructorCatalog lib query)
  { types := types
    components := lib.libraryGroups.map fun entry =>
      (entry.1, component types entry.1 (encodeTy entry.2.1))
    argumentEdges := (queryBindings query).map fun entry =>
      (entry.1, .mk entry.1 top [typeNode entry.2])
    argumentOnly := .node (lib.libraryArgumentOnly.map fun entry =>
      component types entry.1 (encodeTy entry.2))
    avoid := lib.libraryAvoid }

/-- The current two-argument Fun contributes only its argument constructors. -/
theorem constructorsOf_fun2 (argument result : Ty) :
    constructorsOf (.tCons "Fun" [argument, result]) =
      constructorsOf argument ++ constructorsOf result := by
  simp [constructorsOf]

/-- Every other constructor contributes its escaped name and exact arity. -/
theorem constructorsOf_constructor (name : String) (children : List Ty)
    (ordinary : ¬(name = "Fun" ∧ children.length = 2)) :
    constructorsOf (.tCons name children) =
      (escapeConstructor name, children.length) :: children.flatMap constructorsOf := by
  simp [constructorsOf, ordinary]

/-- Every discovered constructor is separate from variables and arrow markers. -/
theorem constructorsOf_separate (typ : Ty) :
    ∀ entry ∈ constructorsOf typ, isVariableSymbol entry.1 = false ∧
      entry.1 ≠ "->" ∧ entry.1 ≠ "(->)" := by
  induction typ using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types, ∀ entry ∈ constructorsOf typ,
      isVariableSymbol entry.1 = false ∧ entry.1 ≠ "->" ∧ entry.1 ≠ "(->)") with
  | tVar _ =>
      intro entry member
      simp only [constructorsOf, List.not_mem_nil] at member
  | tFun _ _ first second =>
      intro entry member
      rw [constructorsOf] at member
      rcases List.mem_append.mp member with own | later
      · exact first entry own
      · exact second entry later
  | tCons name children childIH =>
      intro entry member
      rw [constructorsOf] at member
      rcases List.mem_append.mp member with own | later
      · by_cases alias : name = "Fun" ∧ children.length = 2
        · rw [ite_eq_left alias] at own
          cases own
        · have same : entry = (escapeConstructor name, children.length) := by
            simpa only [alias, ↓reduceIte, List.mem_singleton] using own
          subst entry
          exact escapeConstructor_separate name
      · obtain ⟨child, present, occurs⟩ := List.mem_flatMap.mp later
        exact childIH child present entry occurs
  | nil =>
      rename_i typ member entry occurs
      cases member
  | cons _ _ own later =>
      rename_i typ member entry occurs
      rcases List.mem_cons.mp member with rfl | member
      · exact own entry occurs
      · exact later typ member entry occurs

/-- The full current catalog contains no variable-shaped or arrow-marker constructor. -/
theorem constructorCatalog_separate (lib : Library) (query : Query)
    (entry : String × Nat) (member : entry ∈ constructorCatalog lib query) :
    isVariableSymbol entry.1 = false ∧ entry.1 ≠ "->" ∧ entry.1 ≠ "(->)" := by
  simp only [constructorCatalog, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    or_assoc] at member
  rcases member with ⟨source, _present, found⟩ | ⟨source, _present, found⟩ |
    ⟨source, _present, found⟩ | found
  · exact constructorsOf_separate source.2.1 entry found
  · exact constructorsOf_separate source.2 entry found
  · exact constructorsOf_separate source.2 entry found
  · exact constructorsOf_separate query.queryGoal entry found

/-- Current argument rows retain the original ordered name sequence. -/
theorem context_argument_names (lib : Library) (query : Query) :
    (context lib query).argumentEdges.map Prod.fst = query.queryArguments.map Prod.fst := by
  simpa only [context, List.map_map, Function.comp_def] using queryBindings_names query

/-- Current argument rows retain all original duplicate occurrences. -/
theorem context_argument_length (lib : Library) (query : Query) :
    (context lib query).argumentEdges.length = query.queryArguments.length := by
  simp only [context, List.length_map, queryBindings_length]

/-- The current context uses exactly the universe of its current catalog. -/
theorem context_types (lib : Library) (query : Query) :
    (context lib query).types = allTypes top (constructorCatalog lib query) := rfl

/-- A current rigid type accepts its encoding without a universe premise. -/
theorem typeNode_member (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true) (typ : Ty) :
    evaluate holds [] (mapSyntax literal (typeNode typ)) (candidateRigid typ) := by
  exact SourceSynthesisFiniteTypeWitnesses.typeNode_member holds topHeld (encodeTy typ)

private theorem node_member (holds : Guard → Term Symbol → Bool) (rows : List Row) (row : Row)
    (term : Term Symbol) (selected : row ∈ rows)
    (accepted : evaluate holds [] (mapSyntax literal (.node [row])) term) :
    evaluate holds [] (mapSyntax literal (.node rows)) term := by
  have included : ∀ mapped ∈ mapEdges literal [row], mapped ∈ mapEdges literal rows := by
    rw [mapEdges_eq_map, mapEdges_eq_map]
    intro mapped present
    obtain ⟨source, member, rfl⟩ := List.mem_map.mp present
    have same := List.mem_singleton.mp member
    subst source
    exact List.mem_map.mpr ⟨row, selected, rfl⟩
  rw [mapSyntax, evaluate] at accepted ⊢
  obtain ⟨⟨mapped, member⟩, accepted⟩ := accepted
  exact ⟨⟨mapped, included mapped member⟩, accepted⟩

/-- A last-bound query argument has ordinary typing and actual current leaf membership. -/
theorem query_argument_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool) (name : String) (typ : Ty)
    (found : queryLookup query.queryArguments name = some typ) :
    let term : Term Symbol := .node (literal name) [candidateRigid typ]
    Typed lib query (.var name) typ ∧
      ∃ expression ∈ termsRows (context lib query) asArgument 1,
        evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) term ∧
          term.atPath [0] = some (candidateRigid typ) ∧
          Projection literal Prod.fst term (.var name) ∧
          toProgram literal Prod.fst term = .var name ∧
          (toProgram literal Prod.fst term).components = 1 := by
  have canonical : queryLookup (queryBindings query) name = some typ :=
    (queryBindings_lookup query name).trans found
  have present := queryLookup_member (queryBindings query) name typ canonical
  let row : Row := .mk name top [typeNode typ]
  have selected : row ∈ (context lib query).argumentEdges.map Prod.snd := by
    change row ∈ ((queryBindings query).map fun entry =>
      (entry.1, (.mk entry.1 top [typeNode entry.2] : Row))).map Prod.snd
    rw [List.map_map]
    exact List.mem_map.mpr ⟨(name, typ), present, rfl⟩
  refine ⟨.queryArgument found, .node ((context lib query).argumentEdges.map Prod.snd), ?_,
    ?_, rfl, .component _ _, rfl, rfl⟩
  · rw [SourceSynthesisFirstOrderConstruction.termsRows_one]
    exact List.mem_append.mpr (.inl (by simp))
  · exact node_member (SourceEqualityPCSGuard.holds formulas solver) _ row _ selected
      (SourceSynthesisAnnotatedProgramWitnesses.argument_member formulas solver name (encodeTy typ))

end MicroCFTA.SourceSynthesisCurrentContext
