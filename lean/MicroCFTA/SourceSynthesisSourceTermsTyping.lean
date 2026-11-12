import MicroCFTA.SourceSynthesisAnnotatedProgramWitnesses
import MicroCFTA.SourceSynthesisProgramTermSize

/-!
# Source-admissible annotated Program derivations

These derivations retain the literal FirstOrder source row pools and size
branches. Each component occurrence has its own substitution. Recursive
relevant calls resolve the names of each actual winner's take/drop slices.

Source admissibility adds conditions to ordinary typing. These include
finite universe admission, pruning, argument roles, and names-only winner
selection. This module does not prove that every ordinarily well-typed
Program has such a derivation. Successful output equations identify actual
source results. They do not prove lookup or all-mapM source totality.
-/
namespace MicroCFTA.SourceSynthesisSourceTermsTyping
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top variables)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection)
open SourceSynthesisProgramBuildRolesGeneric
  (mapSyntax mapEdges mapChildren_eq_map mapEdges_eq_map)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

/-- Retain the literal three-child arrow annotation. -/
private abbrev arrow (domain codomain : Term Symbol) : Term Symbol :=
  .node (literal "->") [marker, domain, codomain]

/-- Retain the literal four-child application value. -/
private abbrev appTerm (codomain function argument : Term Symbol) : Term Symbol :=
  .node (literal "app") [codomain, marker, function, argument]

/-- Argument-only rows retain their source order and generalized schemes. -/
def argumentOnlyRows (lib : Library) (query : Query) : List Row :=
  lib.libraryArgumentOnly.map fun entry => component (context lib query).types entry.1 entry.2

/-- The size-one pools include argument-only rows only in an argument cell. -/
def oneRows (lib : Library) (query : Query) (asArgument : Bool) : List Row :=
  ((context lib query).argumentEdges.map Prod.snd ++
    (context lib query).components.map Prod.snd) ++
    (if asArgument then argumentOnlyRows lib query else [])

/-- A restricted size-two function uses only the selected component names. -/
def selectedRows (ctx : Context) (names : List String) : List Row :=
  (ctx.components.filter fun entry => names.contains entry.1).map Prod.snd

/-- A source exclusion removes component rows only. -/
def withoutRows (ctx : Context) (names : List String) : List Row :=
  (ctx.components.filter fun entry => !names.contains entry.1).map Prod.snd

/-- A restricted argument includes rigid arguments and argument-only rows. -/
def restrictedArgumentRows (lib : Library) (query : Query) (excluded : List String) : List Row :=
  (withoutRows (context lib query) excluded ++ (context lib query).argumentEdges.map Prod.snd) ++
    argumentOnlyRows lib query

/-- The fallback excludes all avoided component function names. -/
def fallbackFunctionRows (ctx : Context) : List Row :=
  withoutRows ctx (ctx.avoid.flatMap Prod.fst) ++ ctx.argumentEdges.map Prod.snd

/-- A selected row fixes the Program leaf, annotation, and joint value. -/
inductive LeafTyping (catalog : List (String × Nat)) :
    Row → Program → Term Symbol → Term Symbol → Prop where
  | component (name : String) (typ : Ty) (substitution : String → Term Symbol)
      (images : ∀ key ∈ variables typ, TypeIn catalog (substitution key)) :
      LeafTyping catalog (component (allTypes top catalog) name typ) (.var name)
        (SourceSynthesisGeneralizeFiniteInstances.instantiate substitution typ)
        (.node (literal name) [SourceSynthesisGeneralizeFiniteInstances.instantiate substitution typ])
  | argument (name : String) (typ : Ty) :
      LeafTyping catalog (.mk name top [typeNode top typ]) (.var name) (rigidTerm typ)
        (.node (literal name) [rigidTerm typ])

/-- The derivation follows every literal termsRows branch. -/
inductive TermsTyping (lib : Library) (query : Query) :
    Bool → Nat → Program → Term Symbol → Term Symbol → Prop where
  | leaf {asArgument : Bool} {row : Row} {program : Program} {annotation term : Term Symbol}
      (selected : row ∈ oneRows lib query asArgument)
      (typed : LeafTyping (constructorCatalog lib query) row program annotation term) :
      TermsTyping lib query asArgument 1 program annotation term
  | restricted {asArgument : Bool} {functions excluded : List String}
      {functionRow argumentRow : Row} {functionProgram argumentProgram : Program}
      {domain codomain functionTerm argumentTerm : Term Symbol}
      (avoid : (functions, some excluded) ∈ (context lib query).avoid)
      (selectedFunction : functionRow ∈ selectedRows (context lib query) functions)
      (selectedArgument : argumentRow ∈ restrictedArgumentRows lib query excluded)
      (function : LeafTyping (constructorCatalog lib query) functionRow functionProgram
        (arrow domain codomain) functionTerm)
      (argument : LeafTyping (constructorCatalog lib query) argumentRow argumentProgram domain argumentTerm)
      (result : TypeIn (constructorCatalog lib query) codomain) :
      TermsTyping lib query asArgument 2 (.app functionProgram argumentProgram) codomain
        (appTerm codomain functionTerm argumentTerm)
  | fallback {asArgument : Bool} {functionRow : Row} {functionProgram argumentProgram : Program}
      {domain codomain functionTerm argumentTerm : Term Symbol}
      (selectedFunction : functionRow ∈ fallbackFunctionRows (context lib query))
      (function : LeafTyping (constructorCatalog lib query) functionRow functionProgram
        (arrow domain codomain) functionTerm)
      (argument : TermsTyping lib query true 1 argumentProgram domain argumentTerm)
      (result : TypeIn (constructorCatalog lib query) codomain) :
      TermsTyping lib query asArgument 2 (.app functionProgram argumentProgram) codomain
        (appTerm codomain functionTerm argumentTerm)
  | split {asArgument : Bool} {size left : Nat} {functionProgram argumentProgram : Program}
      {domain codomain functionTerm argumentTerm : Term Symbol}
      (large : 3 ≤ size) (positive : 0 < left) (smaller : left < size)
      (function : TermsTyping lib query false left functionProgram (arrow domain codomain) functionTerm)
      (argument : TermsTyping lib query true (size-left) argumentProgram domain argumentTerm)
      (result : TypeIn (constructorCatalog lib query) codomain) :
      TermsTyping lib query asArgument size (.app functionProgram argumentProgram) codomain
        (appTerm codomain functionTerm argumentTerm)

/-- Relevant derivations retain each actual resolved winner and offset. -/
inductive RelevantTyping (lib : Library) (query : Query) :
    Bool → Nat → List String → Program → Term Symbol → Term Symbol → Prop where
  | empty {asArgument : Bool} {size : Nat} {names : List String}
      {program : Program} {annotation term : Term Symbol}
      (resolved : resolveArguments (context lib query) names = some [])
      (typed : TermsTyping lib query asArgument size program annotation term) :
      RelevantTyping lib query asArgument size names program annotation term
  | singleton {asArgument : Bool} {names : List String} (name : String) (typ : Ty)
      (resolved : resolveArguments (context lib query) names =
        some [(name, .mk name top [typeNode top typ])]) :
      RelevantTyping lib query asArgument 1 names (.var name) (rigidTerm typ)
        (.node (literal name) [rigidTerm typ])
  | split {asArgument : Bool} {size left offset : Nat} {names : List String}
      {arguments : List (String × Row)} {functionProgram argumentProgram : Program}
      {domain codomain functionTerm argumentTerm : Term Symbol}
      (resolved : resolveArguments (context lib query) names = some arguments)
      (nonempty : arguments ≠ []) (enough : arguments.length ≤ size)
      (positive : 0 < left) (smaller : left < size) (offsetBound : offset ≤ arguments.length)
      (function : RelevantTyping lib query false left ((arguments.take offset).map Prod.fst)
        functionProgram (arrow domain codomain) functionTerm)
      (argument : RelevantTyping lib query true (size-left) ((arguments.drop offset).map Prod.fst)
        argumentProgram domain argumentTerm)
      (result : TypeIn (constructorCatalog lib query) codomain) :
      RelevantTyping lib query asArgument size names (.app functionProgram argumentProgram) codomain
        (appTerm codomain functionTerm argumentTerm)

/-- A typed leaf has its exact annotation, projection, and one component. -/
theorem LeafTyping.shape {catalog : List (String × Nat)} {row : Row} {program : Program}
    {annotation term : Term Symbol} (typed : LeafTyping catalog row program annotation term) :
    term.atPath [0] = some annotation ∧ Projection literal Prod.fst term program ∧
      program.components = 1 := by
  cases typed with
  | component name typ substitution images => exact ⟨rfl, .component _ _, rfl⟩
  | argument name typ => exact ⟨rfl, .component _ _, rfl⟩

/-- A terms derivation fixes the annotation, projection, and requested component count. -/
theorem TermsTyping.shape {lib : Library} {query : Query} {asArgument : Bool} {size : Nat}
    {program : Program} {annotation term : Term Symbol}
    (typed : TermsTyping lib query asArgument size program annotation term) :
    term.atPath [0] = some annotation ∧ Projection literal Prod.fst term program ∧
      program.components = size := by
  induction typed with
  | leaf selected typed => exact typed.shape
  | restricted avoid selectedFunction selectedArgument function argument result =>
      exact ⟨rfl, .application _ _ function.shape.2.1 argument.shape.2.1,
        by simp only [Program.components, function.shape.2.2, argument.shape.2.2]⟩
  | fallback selectedFunction function argument result ih =>
      exact ⟨rfl, .application _ _ function.shape.2.1 ih.2.1,
        by simp only [Program.components, function.shape.2.2, ih.2.2]⟩
  | split large positive smaller function argument result firstIH secondIH =>
      refine ⟨rfl, .application _ _ firstIH.2.1 secondIH.2.1, ?_⟩
      simp only [Program.components, firstIH.2.2, secondIH.2.2]
      omega

/-- A relevant derivation fixes the same annotation, projection, and count. -/
theorem RelevantTyping.shape {lib : Library} {query : Query} {asArgument : Bool} {size : Nat}
    {names : List String} {program : Program} {annotation term : Term Symbol}
    (typed : RelevantTyping lib query asArgument size names program annotation term) :
    term.atPath [0] = some annotation ∧ Projection literal Prod.fst term program ∧
      program.components = size := by
  induction typed with
  | empty resolved typed => exact typed.shape
  | singleton name typ resolved => exact ⟨rfl, .component _ _, rfl⟩
  | split resolved nonempty enough positive smaller offsetBound function argument result firstIH secondIH =>
      refine ⟨rfl, .application _ _ firstIH.2.1 secondIH.2.1, ?_⟩
      simp only [Program.components, firstIH.2.2, secondIH.2.2]
      omega

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

private theorem union_member (holds : Guard → Term Symbol → Bool)
    (members : List Expression) (selected : Expression) (term : Term Symbol)
    (present : selected ∈ members)
    (accepted : evaluate holds [] (mapSyntax literal selected) term) :
    evaluate holds [] (mapSyntax literal (.union members)) term := by
  rw [mapSyntax, evaluate]
  refine ⟨⟨mapSyntax literal selected, ?_⟩, accepted⟩
  rw [mapChildren_eq_map]
  exact List.mem_map.mpr ⟨selected, present, rfl⟩

private theorem positiveSplits_complete (size left : Nat) (positive : 0 < left) (smaller : left < size) :
    ∃ split ∈ positiveSplits size, split.val = left := by
  let index : Fin (size-1) := ⟨left-1, by omega⟩
  refine ⟨⟨left, positive, smaller⟩, ?_, rfl⟩
  apply List.mem_map.mpr
  refine ⟨index, List.mem_finRange index, ?_⟩
  apply Subtype.ext
  change left-1+1 = left
  omega

variable [DecidableEq FullSyntax.Formula]

private theorem leaf_member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {catalog : List (String × Nat)}
    {row : Row} {program : Program} {annotation term : Term Symbol}
    (typed : LeafTyping catalog row program annotation term) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal (.node [row])) term := by
  cases typed with
  | component name typ substitution images =>
      exact SourceSynthesisAnnotatedProgramWitnesses.component_member formulas solver catalog
        name typ substitution images
  | argument name typ =>
      exact SourceSynthesisAnnotatedProgramWitnesses.argument_member formulas solver name typ

/-- Every terms derivation belongs to an actual alternative of the source cell. -/
theorem TermsTyping.member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {lib : Library} {query : Query}
    {asArgument : Bool} {size : Nat} {program : Program} {annotation term : Term Symbol}
    (typed : TermsTyping lib query asArgument size program annotation term) :
    ∃ expression ∈ termsRows (context lib query) asArgument size,
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) term := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  induction typed with
  | @leaf asArgument row program annotation term selected typed =>
      have accepted := leaf_member formulas solver typed
      unfold oneRows at selected
      rcases List.mem_append.mp selected with base | optional
      · rcases List.mem_append.mp base with argument | component
        · refine ⟨.node ((context lib query).argumentEdges.map Prod.snd), ?_,
            node_member holds _ row term argument accepted⟩
          rw [termsRows]
          exact List.mem_append.mpr (.inl (by simp))
        · refine ⟨.node ((context lib query).components.map Prod.snd), ?_,
            node_member holds _ row term component accepted⟩
          rw [termsRows]
          exact List.mem_append.mpr (.inl (by simp))
      · cases asArgument with
        | false => cases optional
        | true =>
            refine ⟨(context lib query).argumentOnly, ?_, ?_⟩
            · rw [termsRows]
              exact List.mem_append.mpr (.inr (by simp))
            · exact node_member holds (argumentOnlyRows lib query) row term optional accepted
  | @restricted asArgument functions excluded functionRow argumentRow functionProgram argumentProgram
      domain codomain functionTerm argumentTerm avoid selectedFunction selectedArgument function argument result =>
      let ctx := context lib query
      let functionExpression : Expression := .node (selectedRows ctx functions)
      let argumentExpression : Expression :=
        .union [without ctx excluded, .node (ctx.argumentEdges.map Prod.snd), ctx.argumentOnly]
      have functionMember := node_member holds _ _ _ selectedFunction (leaf_member formulas solver function)
      have argumentMember : evaluate holds [] (mapSyntax literal argumentExpression) argumentTerm := by
        unfold restrictedArgumentRows at selectedArgument
        have accepted := leaf_member formulas solver argument
        rcases List.mem_append.mp selectedArgument with base | only
        · rcases List.mem_append.mp base with component | rigid
          · exact union_member holds _ (without ctx excluded) _ (by simp)
              (node_member holds _ _ _ component accepted)
          · exact union_member holds _ (.node (ctx.argumentEdges.map Prod.snd)) _ (by simp)
              (node_member holds _ _ _ rigid accepted)
        · exact union_member holds _ ctx.argumentOnly _ (by simp)
            (node_member holds _ _ _ only accepted)
      refine ⟨application ctx.types functionExpression argumentExpression, ?_, ?_⟩
      · rw [termsRows]
        apply List.mem_append.mpr
        apply Or.inl
        exact List.mem_filterMap.mpr ⟨(functions, some excluded), avoid, rfl⟩
      · exact SourceSynthesisAnnotatedProgramWitnesses.application_member formulas solver
          (constructorCatalog lib query) functionExpression argumentExpression functionTerm argumentTerm
          domain codomain functionMember argumentMember function.shape.1 argument.shape.1 result
  | @fallback asArgument functionRow functionProgram argumentProgram domain codomain functionTerm argumentTerm
      selectedFunction function argument result ih =>
      let ctx := context lib query
      let functionExpression : Expression :=
        .union [without ctx (ctx.avoid.flatMap Prod.fst), .node (ctx.argumentEdges.map Prod.snd)]
      have functionMember : evaluate holds [] (mapSyntax literal functionExpression) functionTerm := by
        have accepted := leaf_member formulas solver function
        rcases List.mem_append.mp selectedFunction with component | rigid
        · exact union_member holds _ (without ctx (ctx.avoid.flatMap Prod.fst)) _ (by simp)
            (node_member holds _ _ _ component accepted)
        · exact union_member holds _ (.node (ctx.argumentEdges.map Prod.snd)) _ (by simp)
            (node_member holds _ _ _ rigid accepted)
      obtain ⟨selected, included, accepted⟩ := ih
      have argumentMember := union_member holds _ selected _ included accepted
      refine ⟨application ctx.types functionExpression (.union (termsRows ctx true 1)), ?_, ?_⟩
      · have outer : termsRows ctx asArgument 2 =
            ctx.avoid.filterMap (fun (functions, arguments) =>
              arguments.map fun excluded => application ctx.types
                (.node ((ctx.components.filter fun entry => functions.contains entry.1).map Prod.snd))
                (.union [without ctx excluded, .node (ctx.argumentEdges.map Prod.snd), ctx.argumentOnly])) ++
            [application ctx.types functionExpression (.union (termsRows ctx true 1))] := by
          conv => lhs; rw [termsRows]
          all_goals rfl
        rw [outer]
        exact List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl))
      · exact SourceSynthesisAnnotatedProgramWitnesses.application_member formulas solver
          (constructorCatalog lib query) functionExpression (.union (termsRows ctx true 1))
          functionTerm argumentTerm domain codomain functionMember argumentMember
          function.shape.1 argument.shape.1 result
  | @split asArgument size left functionProgram argumentProgram domain codomain functionTerm argumentTerm
      large positive smaller function argument result firstIH secondIH =>
      obtain ⟨split, included, same⟩ := positiveSplits_complete size left positive smaller
      obtain ⟨functionExpression, functionIncluded, functionMember⟩ := firstIH
      obtain ⟨argumentExpression, argumentIncluded, argumentMember⟩ := secondIH
      have functionUnion := union_member holds _ functionExpression _ functionIncluded functionMember
      have argumentUnion := union_member holds _ argumentExpression _ argumentIncluded argumentMember
      let expression := application (context lib query).types
        (.union (termsRows (context lib query) false left))
        (.union (termsRows (context lib query) true (size-left)))
      refine ⟨expression, ?_, ?_⟩
      · obtain ⟨rest, sizeEq⟩ : ∃ rest, size = rest+3 := ⟨size-3, by omega⟩
        subst size
        rw [termsRows]
        apply List.mem_map.mpr
        exact ⟨split, included, by simp only [same]; rfl⟩
      · exact SourceSynthesisAnnotatedProgramWitnesses.application_member formulas solver
          (constructorCatalog lib query) _ _ functionTerm argumentTerm domain codomain
          functionUnion argumentUnion function.shape.1 argument.shape.1 result

end MicroCFTA.SourceSynthesisSourceTermsTyping
