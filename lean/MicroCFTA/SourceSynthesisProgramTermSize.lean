import MicroCFTA.SourceSynthesisProgramSourceSize
import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric
import MicroCFTA.InternedGuardedSyntax

/-!
# Component counts of accepted source terms

The projection follows the source Program roles. A component has one
unrestricted Type child. Application has four children. Filter has two.
The decoder uses these exact arities, as the repaired Haskell toProgram does.
Component count adds variable occurrences. It does not count application
nodes or nodes inside Type annotations.
-/
namespace MicroCFTA.SourceSynthesisProgramTermSize
open Language
open SourceSynthesisFirstOrderConstruction (Expression Row)
open SourceSynthesisProgramSourceSize (ProgramSize RowSize)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges mapEdge
  mapChildren_eq_map mapEdges_eq_map)
open SourceSynthesisGeneralizeSyntax (Guard)
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open InternedNestedConstruction (Syntax)

/-- The source Program result retains variable names and application order. -/
inductive Program where
  | var (name : String)
  | app (function argument : Program)

/-- Count component and argument occurrences, without counting application nodes. -/
def Program.components : Program → Nat
  | .var _ => 1
  | .app function argument => function.components + argument.components

/-- Decode the literal four-child and two-child Program layouts. -/
def toProgram [DecidableEq Symbol] (literal : String → Symbol) (text : Symbol → String) :
    Term Symbol → Program
  | .node symbol [_, _, function, argument] =>
      if symbol = literal "app" then
        .app (toProgram literal text function) (toProgram literal text argument)
      else .var (text symbol)
  | .node symbol [_, candidates] =>
      if symbol = literal "filter" then toProgram literal text candidates else .var (text symbol)
  | .node symbol _ => .var (text symbol)

/-- A role-directed projection records the actual accepted Program children. -/
inductive Projection (literal : String → Symbol) (text : Symbol → String) :
    Term Symbol → Program → Prop where
  | component (symbol : Symbol) (annotation : Term Symbol) :
      Projection literal text (.node symbol [annotation]) (.var (text symbol))
  | application (annotation marker : Term Symbol)
      {function argument : Term Symbol} {projectedFunction projectedArgument : Program}
      (first : Projection literal text function projectedFunction)
      (second : Projection literal text argument projectedArgument) :
      Projection literal text (.node (literal "app") [annotation, marker, function, argument])
        (.app projectedFunction projectedArgument)
  | filter (goal : Term Symbol) {candidates : Term Symbol} {program : Program}
      (candidate : Projection literal text candidates program) :
      Projection literal text (.node (literal "filter") [goal, candidates]) program

/-- Exact arities make the literal decoder agree with every source-role projection. -/
theorem Projection.toProgram_eq [DecidableEq Symbol] {literal : String → Symbol}
    {text : Symbol → String} {term : Term Symbol} {program : Program}
    (projected : Projection literal text term program) : toProgram literal text term = program := by
  induction projected with
  | component symbol annotation => rfl
  | application annotation marker first second firstIH secondIH =>
      simp only [toProgram, ↓reduceIte, firstIH, secondIH]
  | filter goal candidate ih => simp only [toProgram, ↓reduceIte, ih]

private theorem forest_cons (holds : Guard → Term Symbol → Bool)
    (environment : List (BinderLanguage.Lang Symbol)) (child : Syntax Symbol Guard)
    (children : List (Syntax Symbol Guard)) (terms : List (Term Symbol))
    (accepted : forest holds environment (child :: children) terms) :
    ∃ term rest, terms = term :: rest ∧ evaluate holds environment child term ∧
      forest holds environment children rest := by
  cases terms with
  | nil => simp only [forest] at accepted
  | cons term rest => exact ⟨term, rest, rfl, by simpa only [forest] using accepted⟩

private theorem forest_nil (holds : Guard → Term Symbol → Bool)
    (environment : List (BinderLanguage.Lang Symbol)) (terms : List (Term Symbol))
    (accepted : forest holds environment [] terms) : terms = [] := by
  cases terms with
  | nil => rfl
  | cons term rest => simp only [forest] at accepted

private theorem source_projection (literal : String → Symbol) (text : Symbol → String)
    {count : Nat} {expression : Expression} (sized : ProgramSize count expression) :
    ∀ holds environment term, evaluate holds environment (mapSyntax literal expression) term →
      ∃ program, Projection literal text term program ∧ program.components = count := by
  induction sized using ProgramSize.rec
    (motive_2 := fun count row _ => ∀ holds environment term,
      edgeMeaning holds environment (mapEdge literal row) term →
        ∃ program, Projection literal text term program ∧ program.components = count) with
  | empty count =>
      intro holds environment term accepted
      simp only [mapSyntax, evaluate] at accepted
  | node rows _ checked =>
      intro holds environment term accepted
      rw [mapSyntax, evaluate] at accepted
      obtain ⟨selected, accepted⟩ := accepted
      have member : selected.val ∈ rows.map (mapEdge literal) := by
        simpa only [mapEdges_eq_map] using selected.property
      obtain ⟨row, included, same⟩ := List.mem_map.mp member
      exact checked row included holds environment term (by simpa only [same] using accepted)
  | union members _ checked =>
      intro holds environment term accepted
      rw [mapSyntax, evaluate] at accepted
      obtain ⟨selected, accepted⟩ := accepted
      have member : selected.val ∈ members.map (mapSyntax literal) := by
        simpa only [mapChildren_eq_map] using selected.property
      obtain ⟨expression, included, same⟩ := List.mem_map.mp member
      exact checked expression included holds environment term (by simpa only [same] using accepted)
  | annotated name annotation =>
      rename_i holds environment term accepted
      simp only [mapEdge, mapChildren, edgeMeaning] at accepted
      obtain ⟨terms, shape, accepted, _guard⟩ := accepted
      obtain ⟨annotationTerm, rest, rfl, _typed, tail⟩ := forest_cons _ _ _ _ _ accepted
      have nilTail := forest_nil _ _ _ tail
      subst rest
      subst term
      exact ⟨.var (text (literal name)), .component _ annotationTerm, rfl⟩
  | @application functionCount argumentCount types function argument row actual _ _ functionIH argumentIH =>
      rename_i holds environment term accepted
      have same := (List.cons.inj (Syntax.node.inj actual)).1
      subst row
      simp only [mapEdge, mapChildren, edgeMeaning] at accepted
      obtain ⟨terms, shape, accepted, _guard⟩ := accepted
      obtain ⟨annotationTerm, rest, rfl, _typed, accepted⟩ := forest_cons _ _ _ _ _ accepted
      obtain ⟨markerTerm, rest, rfl, _marker, accepted⟩ := forest_cons _ _ _ _ _ accepted
      obtain ⟨functionTerm, rest, rfl, functionAccepted, accepted⟩ := forest_cons _ _ _ _ _ accepted
      obtain ⟨argumentTerm, rest, rfl, argumentAccepted, tail⟩ := forest_cons _ _ _ _ _ accepted
      have nilTail := forest_nil _ _ _ tail
      subst rest
      subst term
      obtain ⟨projectedFunction, first, firstCount⟩ := functionIH holds environment functionTerm functionAccepted
      obtain ⟨projectedArgument, second, secondCount⟩ := argumentIH holds environment argumentTerm argumentAccepted
      exact ⟨.app projectedFunction projectedArgument, .application annotationTerm markerTerm first second,
        by simp only [Program.components, firstCount, secondCount]⟩
  | @filter count candidates goal row actual _ candidateIH =>
      rename_i holds environment term accepted
      have same := (List.cons.inj (Syntax.node.inj actual)).1
      subst row
      simp only [mapEdge, mapChildren, edgeMeaning] at accepted
      obtain ⟨terms, shape, accepted, _guard⟩ := accepted
      obtain ⟨goalTerm, rest, rfl, _typed, accepted⟩ := forest_cons _ _ _ _ _ accepted
      obtain ⟨candidateTerm, rest, rfl, candidateAccepted, tail⟩ := forest_cons _ _ _ _ _ accepted
      have nilTail := forest_nil _ _ _ tail
      subst rest
      subst term
      obtain ⟨program, projected, counted⟩ := candidateIH holds environment candidateTerm candidateAccepted
      exact ⟨program, .filter goalTerm projected, counted⟩

/-- Actual guarded source acceptance derives a projected Program with the requested count. -/
theorem accepted_projection (literal : String → Symbol) (text : Symbol → String)
    {count : Nat} {expression : Expression} (sized : ProgramSize count expression)
    (holds : Guard → Term Symbol → Bool) (environment : List (BinderLanguage.Lang Symbol))
    (term : Term Symbol) (accepted : evaluate holds environment (mapSyntax literal expression) term) :
    ∃ program, Projection literal text term program ∧ program.components = count :=
  source_projection literal text sized holds environment term accepted

/-- The repaired literal decoder counts exactly the source Program components. -/
theorem accepted_toProgram [DecidableEq Symbol] (literal : String → Symbol)
    (text : Symbol → String) {count : Nat} {expression : Expression}
    (sized : ProgramSize count expression) (holds : Guard → Term Symbol → Bool)
    (environment : List (BinderLanguage.Lang Symbol)) (term : Term Symbol)
    (accepted : evaluate holds environment (mapSyntax literal expression) term) :
    (toProgram literal text term).components = count := by
  obtain ⟨program, projected, counted⟩ := accepted_projection literal text sized holds environment term accepted
  rw [projected.toProgram_eq]
  exact counted

end MicroCFTA.SourceSynthesisProgramTermSize
