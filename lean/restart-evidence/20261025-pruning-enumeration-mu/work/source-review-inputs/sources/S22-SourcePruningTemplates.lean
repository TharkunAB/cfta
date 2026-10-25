import MicroCFTA.SourcePruningPartialMatch
import MicroCFTA.Fragments
import MicroCFTA.SourceObservations
import MicroCFTA.FormulaExecutable

/-!
# Pure helpers for the partial pruning oracle

Full labels retain source names and refinements. Tagged finite buckets
represent the observable lookup and ascending traversal of the source maps.
-/
namespace MicroCFTA.SourcePruningTemplates
open Language Fragments EnumerationState SourcePruningPartialMatch
attribute [local instance] FormulaExecutable.formulaDecidableEq

/-- The existing complete source alphabet, including refinements. -/
abbrev Symbol := SourceObservations.Label FullSyntax.Formula

/-- A partial term with full labels, raw holes and truncation. -/
abbrev PartialTerm := Language.Term (EnumerationState.PartialSymbol Symbol)

/-- View a fragment without reading or expanding any hole. -/
def fragmentTerm : Fragment Symbol → PartialTerm
  | .node symbol children => .node (.concrete symbol) (children.map fragmentTerm)
  | .hole uv => .node (.hole uv) []

/-- Select application terms in function-before-argument order. -/
def programs : PartialTerm → List PartialTerm
  | .node (.concrete symbol) [_, term] =>
      if symbol = ("filter", FullSyntax.Formula.top) then programs term else []
  | term@(.node (.concrete symbol) [_, _, function, argument]) =>
      if symbol = ("app", FullSyntax.Formula.top) then
        term :: programs function ++ programs argument
      else []
  | _ => []

private def templateSpineFrom (count : Nat) : Template.Pattern Symbol → Option (Symbol × Nat)
  | .node symbol [_, _, function, _] =>
      if symbol = ("app", FullSyntax.Formula.top) then templateSpineFrom (count + 1) function else none
  | .node symbol [_] => some (symbol, count)
  | _ => none

/-- Read only exact raw application nodes and a one-child template head. -/
def templateSpine (pattern : Template.Pattern Symbol) : Option (Symbol × Nat) :=
  templateSpineFrom 0 pattern

private def partialSpineFrom (count : Nat) : PartialTerm → Option (Symbol × Nat)
  | .node (.concrete symbol) [_, _, function, _] =>
      if symbol = ("app", FullSyntax.Formula.top) then partialSpineFrom (count + 1) function else none
  | .node (.concrete symbol) [_] => some (symbol, count)
  | _ => none

/-- Read only exact raw application nodes and a one-child concrete head. -/
def partialSpine (term : PartialTerm) : Option (Symbol × Nat) :=
  partialSpineFrom 0 term

/-- Select the ascending-position union of generic and matching fixed buckets. -/
def indexTemplates (templates : List (Template.Pattern Symbol)) (term : PartialTerm) :
    List (Template.Pattern Symbol) :=
  let tagged := templates.zipIdx
  let generic := tagged.filter (fun entry => (templateSpine entry.1).isNone)
  let fixed := fun key => tagged.filter (fun entry => decide (templateSpine entry.1 = some key))
  match partialSpine term with
  | none => templates
  | some key =>
      (List.range templates.length).filterMap fun position =>
        ((generic.find? (fun entry => entry.2 == position)).map Prod.fst).orElse
          (fun _ => ((fixed key).find? (fun entry => entry.2 == position)).map Prod.fst)

private def structuralProgram : Template.Pattern Symbol → Option (Template.Pattern Symbol)
  | .hole => some .hole
  | .node symbol [.hole, marker, function, argument] =>
      if symbol = ("app", FullSyntax.Formula.top) then
        if (match marker with
          | .hole => true
          | .node arrow [] => decide (arrow = ("(->)", FullSyntax.Formula.top))
          | _ => false) then do
          let nextFunction ← structuralProgram function
          let nextArgument ← structuralProgram argument
          pure (.node ("app", FullSyntax.Formula.top) [.hole, .hole, nextFunction, nextArgument])
        else none
      else none
  | .node symbol [.hole] => some (.node symbol [.hole])
  | _ => none

/-- Admit only a root application with the source's annotation restrictions. -/
def structuralTemplate : Template.Pattern Symbol → Option (Template.Pattern Symbol)
  | pattern@(.node symbol [_, _, _, _]) =>
      if symbol = ("app", FullSyntax.Formula.top) then structuralProgram pattern else none
  | _ => none

/-- Recognize the exact ordinary application and filter root shapes. -/
def isProgramRoot : Fragment Symbol → Bool
  | .node symbol [_, _, _, _] => decide (symbol = ("app", FullSyntax.Formula.top))
  | .node symbol [_, _] => decide (symbol = ("filter", FullSyntax.Formula.top))
  | _ => false

/-- Check only the exact application and filter roots used by the early path. -/
def rejectEarly (templates : List (Template.Pattern Symbol)) (fragment : Fragment Symbol) : Bool :=
  if isProgramRoot fragment then
    let early := templates.filterMap structuralTemplate
    (programs (fragmentTerm fragment)).any fun term =>
      (indexTemplates early term).any fun pattern =>
        match matchPartial pattern term with
        | some [] => true
        | _ => false
  else false

/-- Start every indexed match in program order and then template order. -/
def startMatches (templates : List (Template.Pattern Symbol)) (term : PartialTerm) :
    List (Option (Pending Symbol)) :=
  (programs term).flatMap fun program =>
    (indexTemplates templates program).map fun pattern => matchPartial pattern program

/-- Combine resumed and new results without dropping repeated nonempty checks. -/
def finishChecks (resumed started : List (Option (Pending Symbol))) : Bool × List (Pending Symbol) :=
  let checks := (resumed ++ started).filterMap id
  (checks.any (fun pending => pending.isEmpty), checks.filter (fun pending => !pending.isEmpty))

/-- Choose the first candidate named by any raw pending hole. -/
def order (pending : List (Pending Symbol)) (candidates : List Nat) : Option Nat :=
  let waiting := (pending.flatMap id).map Prod.snd
  candidates.find? (fun uv => waiting.contains uv)

/-- An unknown program head uses the original catalog with its duplicates. -/
theorem indexTemplates_unknown (templates : List (Template.Pattern Symbol)) (term : PartialTerm)
    (unknown : partialSpine term = none) : indexTemplates templates term = templates := by
  simp only [indexTemplates, unknown]

/-- A known head uses the tagged finite-map union in ascending original positions. -/
theorem indexTemplates_known (templates : List (Template.Pattern Symbol)) (term : PartialTerm)
    (key : Symbol × Nat) (known : partialSpine term = some key) :
    indexTemplates templates term =
      let tagged := templates.zipIdx
      let generic := tagged.filter (fun entry => (templateSpine entry.1).isNone)
      let fixed := tagged.filter (fun entry => decide (templateSpine entry.1 = some key))
      (List.range templates.length).filterMap fun position =>
        ((generic.find? (fun entry => entry.2 == position)).map Prod.fst).orElse
          (fun _ => (fixed.find? (fun entry => entry.2 == position)).map Prod.fst) := by
  simp only [indexTemplates, known]

/-- A raw fragment hole keeps its original ID in the pure view. -/
theorem fragmentTerm_hole (uv : Nat) : fragmentTerm (.hole uv) = .node (.hole uv) [] := by
  simp only [fragmentTerm]

/-- A filter contributes only the programs of its program child. -/
theorem programs_filter (annotation term : PartialTerm) :
    programs (.node (.concrete ("filter", FullSyntax.Formula.top)) [annotation, term]) = programs term := by
  simp only [programs, ↓reduceIte]

/-- An application precedes the programs in its function and argument. -/
theorem programs_app (annotation marker function argument : PartialTerm) :
    programs (.node (.concrete ("app", FullSyntax.Formula.top)) [annotation, marker, function, argument]) =
      .node (.concrete ("app", FullSyntax.Formula.top)) [annotation, marker, function, argument] ::
        programs function ++ programs argument := by
  simp only [programs, ↓reduceIte]

/-- The early path does not inspect a raw fragment hole. -/
theorem rejectEarly_hole (templates : List (Template.Pattern Symbol)) (uv : Nat) :
    rejectEarly templates (.hole uv) = false := by
  rfl

/-- There is no match to prune or retain when both result lists are empty. -/
theorem finishChecks_nil : finishChecks [] [] = (false, []) := by
  rfl

/-- An empty candidate list offers no waiting hole. -/
theorem order_nil (pending : List (Pending Symbol)) : order pending [] = none := by
  rfl

end MicroCFTA.SourcePruningTemplates
