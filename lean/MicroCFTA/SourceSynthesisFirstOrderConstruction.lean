import MicroCFTA.SourceSynthesisGeneralizeSyntax
import MicroCFTA.SourceSynthesisSelections

/-!
# FirstOrder synthesis construction from the actual source rows

This module retains the source's component, application, filter, and table
rows. Relevant lookup selects the last entry with the requested names. This
matters when query argument names repeat. Recursive value evaluation uses
strictly smaller sizes; it does not take execution fuel.

The result is a constructor instruction expression. Native normalization,
cache effects, sharing, lazy demand, and machine Int conversion are separate.
This is the FirstOrder branch. It does not implement the Curried branch.
-/
namespace MicroCFTA.SourceSynthesisFirstOrderConstruction

open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard generalize)
open InternedNestedConstruction (Syntax EdgeSyntax)

abbrev Expression := Expr Guard
abbrev Row := EdgeSyntax String Guard

/-- A missing source table key retains its flag, signed size, and names. -/
inductive MissingKey where
  | terms (asArgument : Bool) (size : Int)
  | relevant (asArgument : Bool) (size : Int) (names : List String)
  deriving DecidableEq

/-- The source discovers constructor/arity pairs in their first occurrence order. -/
def constructorCatalog (lib : Library) (query : Query) : List (String × Nat) :=
  (lib.libraryGroups.flatMap (fun entry => constructorsOf entry.2.1) ++
    lib.libraryArgumentOnly.flatMap (fun entry => constructorsOf entry.2) ++
    query.queryArguments.flatMap (fun entry => constructorsOf entry.2) ++
    constructorsOf query.queryGoal).eraseDups

/-- This is the source FirstOrder typesOf branch with its default recursive universe. -/
def typesOf (lib : Library) (query : Query) : Expression :=
  allTypes top (constructorCatalog lib query)

/-- A component generalizes its type; query argument rows remain rigid. -/
def component (types : Expression) (name : String) (typ : Ty) : Row :=
  .mk name top [generalize types typ]

/-- Source application children and all three equality classes retain their order. -/
def application (types function argument : Expression) : Expression :=
  .node [.mk "app" (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
    [types, arrowMarker top, function, argument]]

/-- The source filter ties its goal child to the program's annotation child. -/
def ofType (candidates goal : Expression) : Expression :=
  .node [.mk "filter" (eqGuard [[[0], [1, 0]]]) [goal, candidates]]

/-- The source's immutable local values are computed from its actual input data. -/
structure Context where
  types : Expression
  components : List (String × Row)
  argumentEdges : List (String × Row)
  argumentOnly : Expression
  avoid : List (List String × Option (List String))

/-- Build the literal FirstOrder local bindings without a caller invariant. -/
def context (lib : Library) (query : Query) : Context :=
  let types := typesOf lib query
  { types := types
    components := lib.libraryGroups.map fun entry =>
      (entry.1, component types entry.1 entry.2.1)
    argumentEdges := query.queryArguments.map fun entry =>
      (entry.1, .mk entry.1 top [typeNode top entry.2])
    argumentOnly := .node (lib.libraryArgumentOnly.map fun entry => component types entry.1 entry.2)
    avoid := lib.libraryAvoid }

/-- Only library component names are removed by source without. -/
def without (ctx : Context) (names : List String) : Expression :=
  .node ((ctx.components.filter fun entry => !names.contains entry.1).map Prod.snd)

/-- The positive split loop is the source ascending range one through size minus one. -/
def positiveSplits (size : Nat) : List {left : Nat // 0 < left ∧ left < size} :=
  (List.finRange (size - 1)).map fun index =>
    ⟨index.val + 1, by omega, by have bound := index.isLt; omega⟩

/-- Evaluate the unique terms-table cells by their actual decreasing dependencies. -/
def termsRows (ctx : Context) (asArgument : Bool) (size : Nat) : List Expression :=
  match size with
  | 0 => []
  | 1 => [.node (ctx.argumentEdges.map Prod.snd), .node (ctx.components.map Prod.snd)] ++
      (if asArgument then [ctx.argumentOnly] else [])
  | 2 =>
      ctx.avoid.filterMap (fun (functions, arguments) =>
        arguments.map fun excluded => application ctx.types
          (.node ((ctx.components.filter fun entry => functions.contains entry.1).map Prod.snd))
          (.union [without ctx excluded, .node (ctx.argumentEdges.map Prod.snd), ctx.argumentOnly])) ++
      [application ctx.types
        (.union [without ctx (ctx.avoid.flatMap Prod.fst), .node (ctx.argumentEdges.map Prod.snd)])
        (.union (termsRows ctx true 1))]
  | rest + 3 =>
      (positiveSplits (rest + 3)).map fun split =>
        application ctx.types
          (.union (termsRows ctx false split.val))
          (.union (termsRows ctx true (rest + 3 - split.val)))
termination_by size
decreasing_by
  all_goals simp_wf
  all_goals first | omega | exact split.property.2

/-- Source selection keys are names; repeated names retain the last source entry. -/
def resolveArguments (ctx : Context) (names : List String) : Option (List (String × Row)) :=
  SourceSynthesisSelections.resolveSelection ctx.argumentEdges names

/-- Evaluate relevant-table cells after source name-key resolution. -/
def relevantRows (ctx : Context) (asArgument : Bool) (size : Nat) (names : List String) :
    Except MissingKey (List Expression) := do
  let arguments ← match resolveArguments ctx names with
    | none => .error (.relevant asArgument (Int.ofNat size) names)
    | some arguments => .ok arguments
  match _sizeCase : size, arguments with
  | _, [] => pure (termsRows ctx asArgument size)
  | 1, [(_, edge)] => pure [.node [edge]]
  | _, _ =>
      if size < arguments.length then pure []
      else do
        let rows ← (positiveSplits size).mapM fun split => do
          let choices ← (List.range (arguments.length + 1)).mapM fun offset => do
            let used := (arguments.take offset).map Prod.fst
            let remaining := (arguments.drop offset).map Prod.fst
            let function ← relevantRows ctx false split.val used
            let argument ← relevantRows ctx true (size - split.val) remaining
            pure (application ctx.types (.union function) (.union argument))
          pure choices
        pure rows.flatten
termination_by size
decreasing_by
  all_goals simp_wf
  all_goals have bounds := split.property
  all_goals simp_all
  all_goals omega

/-- Evaluate the source root permutations and filter at a signed size request. -/
def firstOrderRaw (lib : Library) (query : Query) (size : Int) : Except MissingKey Expression := do
  let ctx := context lib query
  if size < 0 then
    .error (.relevant true size (query.queryArguments.map Prod.fst))
  else do
    let rows ← (SourceSynthesisSelections.permutations ctx.argumentEdges).mapM fun arguments =>
      relevantRows ctx true size.toNat (arguments.map Prod.fst)
    pure (ofType (.union rows.flatten) (typeNode top query.queryGoal))

/-- A negative request fails its missing relevant-table lookup before a cell is evaluated. -/
theorem firstOrderRaw_negative (lib : Library) (query : Query) (size : Int) (negative : size < 0) :
    firstOrderRaw lib query size = .error (.relevant true size (query.queryArguments.map Prod.fst)) := by
  simp [firstOrderRaw, negative]

/-- The actual zero-size terms cell exists and contains no rows. -/
theorem termsRows_zero (ctx : Context) (asArgument : Bool) : termsRows ctx asArgument 0 = [] := by
  simp [termsRows]

/-- The size-one cells retain argument-only components only in argument position. -/
theorem termsRows_one (ctx : Context) (asArgument : Bool) :
    termsRows ctx asArgument 1 =
      [.node (ctx.argumentEdges.map Prod.snd), .node (ctx.components.map Prod.snd)] ++
        (if asArgument then [ctx.argumentOnly] else []) := by
  simp [termsRows]

end MicroCFTA.SourceSynthesisFirstOrderConstruction
