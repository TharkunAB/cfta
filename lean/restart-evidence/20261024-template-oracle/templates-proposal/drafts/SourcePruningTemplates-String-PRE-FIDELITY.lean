import MicroCFTA.SourcePruningPartialMatch
import MicroCFTA.Fragments

/-!
# Pure helpers for the partial pruning oracle

String represents the ordinary source symbol names. Tagged finite buckets
represent the observable lookup and ascending traversal of the source maps.
-/
namespace MicroCFTA.SourcePruningTemplates
open Language Fragments EnumerationState SourcePruningPartialMatch

/-- A partial term with concrete names, raw holes and truncation. -/
abbrev PartialTerm := Language.Term (EnumerationState.PartialSymbol String)

/-- View a fragment without reading or expanding any hole. -/
def fragmentTerm : Fragment String → PartialTerm
  | .node symbol children => .node (.concrete symbol) (children.map fragmentTerm)
  | .hole uv => .node (.hole uv) []

/-- Select application terms in function-before-argument order. -/
def programs : PartialTerm → List PartialTerm
  | .node (.concrete "filter") [_, term] => programs term
  | term@(.node (.concrete "app") [_, _, function, argument]) =>
      term :: programs function ++ programs argument
  | _ => []

private def templateSpineFrom (count : Nat) : Template.Pattern String → Option (String × Nat)
  | .node "app" [_, _, function, _] => templateSpineFrom (count + 1) function
  | .node symbol [_] => some (symbol, count)
  | _ => none

/-- Read only exact raw application nodes and a one-child template head. -/
def templateSpine (pattern : Template.Pattern String) : Option (String × Nat) :=
  templateSpineFrom 0 pattern

private def partialSpineFrom (count : Nat) : PartialTerm → Option (String × Nat)
  | .node (.concrete "app") [_, _, function, _] => partialSpineFrom (count + 1) function
  | .node (.concrete symbol) [_] => some (symbol, count)
  | _ => none

/-- Read only exact raw application nodes and a one-child concrete head. -/
def partialSpine (term : PartialTerm) : Option (String × Nat) :=
  partialSpineFrom 0 term

/-- Select the ascending-position union of generic and matching fixed buckets. -/
def indexTemplates (templates : List (Template.Pattern String)) (term : PartialTerm) :
    List (Template.Pattern String) :=
  let tagged := templates.zipIdx
  let generic := tagged.filter (fun entry => (templateSpine entry.1).isNone)
  let fixed := fun key => tagged.filter (fun entry => templateSpine entry.1 == some key)
  match partialSpine term with
  | none => templates
  | some key =>
      (List.range templates.length).filterMap fun position =>
        ((generic.find? (fun entry => entry.2 == position)).map Prod.fst).orElse
          (fun _ => (fixed key |>.find? (fun entry => entry.2 == position)).map Prod.fst)

private def structuralProgram : Template.Pattern String → Option (Template.Pattern String)
  | .hole => some .hole
  | .node "app" [.hole, marker, function, argument] =>
      if (match marker with | .hole | .node "(->)" [] => true | _ => false) then do
        let nextFunction ← structuralProgram function
        let nextArgument ← structuralProgram argument
        pure (.node "app" [.hole, .hole, nextFunction, nextArgument])
      else none
  | .node symbol [.hole] => some (.node symbol [.hole])
  | _ => none

/-- Admit only a root application with the source's annotation restrictions. -/
def structuralTemplate : Template.Pattern String → Option (Template.Pattern String)
  | pattern@(.node "app" [_, _, _, _]) => structuralProgram pattern
  | _ => none

/-- Check only the exact application and filter roots used by the early path. -/
def rejectEarly (templates : List (Template.Pattern String)) (fragment : Fragment String) : Bool :=
  match fragment with
  | .node "app" [_, _, _, _] | .node "filter" [_, _] =>
      let early := templates.filterMap structuralTemplate
      (programs (fragmentTerm fragment)).any fun term =>
        (indexTemplates early term).any fun pattern =>
          match matchPartial pattern term with
          | some [] => true
          | _ => false
  | _ => false

/-- Start every indexed match in program order and then template order. -/
def startMatches (templates : List (Template.Pattern String)) (term : PartialTerm) :
    List (Option (Pending String)) :=
  (programs term).flatMap fun program =>
    (indexTemplates templates program).map fun pattern => matchPartial pattern program

/-- Combine resumed and new results without dropping repeated nonempty checks. -/
def finishChecks (resumed started : List (Option (Pending String))) : Bool × List (Pending String) :=
  let checks := (resumed ++ started).filterMap id
  (checks.any (fun pending => pending.isEmpty), checks.filter (fun pending => !pending.isEmpty))

/-- Choose the first candidate named by any raw pending hole. -/
def order (pending : List (Pending String)) (candidates : List Nat) : Option Nat :=
  let waiting := (pending.flatMap id).map Prod.snd
  candidates.find? (fun uv => waiting.contains uv)

/-- An unknown program head uses the original catalog with its duplicates. -/
theorem indexTemplates_unknown (templates : List (Template.Pattern String)) (term : PartialTerm)
    (unknown : partialSpine term = none) : indexTemplates templates term = templates := by
  simp only [indexTemplates, unknown]

/-- A known head uses the tagged finite-map union in ascending original positions. -/
theorem indexTemplates_known (templates : List (Template.Pattern String)) (term : PartialTerm)
    (key : String × Nat) (known : partialSpine term = some key) :
    indexTemplates templates term =
      let tagged := templates.zipIdx
      let generic := tagged.filter (fun entry => (templateSpine entry.1).isNone)
      let fixed := tagged.filter (fun entry => templateSpine entry.1 == some key)
      (List.range templates.length).filterMap fun position =>
        ((generic.find? (fun entry => entry.2 == position)).map Prod.fst).orElse
          (fun _ => (fixed.find? (fun entry => entry.2 == position)).map Prod.fst) := by
  simp only [indexTemplates, known]

/-- A raw fragment hole keeps its original ID in the pure view. -/
theorem fragmentTerm_hole (uv : Nat) : fragmentTerm (.hole uv) = .node (.hole uv) [] := by
  rfl

/-- A filter contributes only the programs of its program child. -/
theorem programs_filter (annotation term : PartialTerm) :
    programs (.node (.concrete "filter") [annotation, term]) = programs term := by
  rfl

/-- An application precedes the programs in its function and argument. -/
theorem programs_app (annotation marker function argument : PartialTerm) :
    programs (.node (.concrete "app") [annotation, marker, function, argument]) =
      .node (.concrete "app") [annotation, marker, function, argument] ::
        programs function ++ programs argument := by
  rfl

/-- The early path does not inspect a raw fragment hole. -/
theorem rejectEarly_hole (templates : List (Template.Pattern String)) (uv : Nat) :
    rejectEarly templates (.hole uv) = false := by
  rfl

/-- There is no match to prune or retain when both result lists are empty. -/
theorem finishChecks_nil : finishChecks [] [] = (false, []) := by
  rfl

/-- An empty candidate list offers no waiting hole. -/
theorem order_nil (pending : List (Pending String)) : order pending [] = none := by
  rfl

end MicroCFTA.SourcePruningTemplates
