import MicroCFTA.SourcePruningTemplates
import MicroCFTA.EnumerationBuilderCaches

/-!
# Pure positions in partial pruning programs

Full labels distinguish ordinary app/4 and filter/2 nodes from refined labels.
Type IDs use the existing ascending set view. Program holes retain raw IDs,
order and duplicates. Native Int bounds, decimal formatting and extraction
from Haskell values remain explicit correspondence boundaries.
-/
namespace MicroCFTA.SourcePruningPositions
open Language Fragments EnumerationState SourcePruningTemplates
open EnumerationBuilderCaches
attribute [local instance] FormulaExecutable.formulaDecidableEq

/-- Insert raw holes at type positions with the source's nested right folds. -/
def typePositions (isType : Bool) (fragment : Fragment Symbol) (types : List Nat) : List Nat :=
  match fragment with
  | .hole uv => if isType then canonicalIds (uv :: types) else types
  | .node symbol children =>
      if isType then children.foldr (fun child accumulated => typePositions true child accumulated) types
      else match children with
        | [annotation, marker, function, argument] =>
            if symbol = ("app", FullSyntax.Formula.top) then
              typePositions true annotation (typePositions true marker
                (typePositions false function (typePositions false argument types)))
            else typePositions true annotation (typePositions true marker
              (typePositions true function (typePositions true argument types)))
        | [annotation, term] =>
            if symbol = ("filter", FullSyntax.Formula.top) then
              typePositions true annotation (typePositions false term types)
            else typePositions true annotation (typePositions true term types)
        | children => children.foldr (fun child accumulated => typePositions true child accumulated) types
termination_by sizeOf fragment

/-- Read program holes in function-before-argument order without normalization. -/
def programHoles (isType : Bool) (fragment : Fragment Symbol) : List Nat :=
  match fragment with
  | .hole uv => if isType then [] else [uv]
  | .node symbol children =>
      if isType then []
      else match children with
        | [_, _, function, argument] =>
            if symbol = ("app", FullSyntax.Formula.top) then
              programHoles false function ++ programHoles false argument
            else []
        | [_, term] =>
            if symbol = ("filter", FullSyntax.Formula.top) then programHoles false term else []
        | _ => []

/-- Replace partial holes by the exact type, raw program-ID or recursion marker. -/
def openProgram (isType : Bool) (term : SourcePruningTemplates.PartialTerm) : Term Symbol :=
  match term with
  | .node (.hole uv) _ =>
      if isType then .node ("?", FullSyntax.Formula.top) []
      else .node ("?program#" ++ toString uv, FullSyntax.Formula.top) []
  | .node .truncated _ => .node ("Mu", FullSyntax.Formula.top) []
  | .node (.concrete symbol) children =>
      if isType then .node symbol (children.map (fun child => openProgram true child))
      else match children with
        | [annotation, marker, function, argument] =>
            if symbol = ("app", FullSyntax.Formula.top) then
              .node symbol [openProgram true annotation, openProgram true marker,
                openProgram false function, openProgram false argument]
            else .node symbol [openProgram true annotation, openProgram true marker,
              openProgram true function, openProgram true argument]
        | [annotation, term] =>
            if symbol = ("filter", FullSyntax.Formula.top) then
              .node symbol [openProgram true annotation, openProgram false term]
            else .node symbol [openProgram true annotation, openProgram true term]
        | children => .node symbol (children.map (fun child => openProgram true child))
termination_by sizeOf term

/-- A type-position hole inserts its own raw ID into the observable set. -/
theorem typePositions_hole_true (uv : Nat) (types : List Nat) :
    typePositions true (.hole uv) types = canonicalIds (uv :: types) := by
  simp [typePositions]

/-- A program-position hole leaves the type set unchanged. -/
theorem typePositions_hole_false (uv : Nat) (types : List Nat) :
    typePositions false (.hole uv) types = types := by
  simp [typePositions]

/-- Insertion adds exactly the raw hole ID and preserves each earlier member. -/
theorem typePositions_hole_member (uv identity : Nat) (types : List Nat) :
    identity ∈ typePositions true (.hole uv) types ↔ identity = uv ∨ identity ∈ types := by
  rw [typePositions_hole_true, canonicalIds_member]
  exact List.mem_cons

/-- A type-hole insertion has no repeated ID. -/
theorem typePositions_hole_nodup (uv : Nat) (types : List Nat) :
    (typePositions true (.hole uv) types).Nodup := by
  rw [typePositions_hole_true]
  exact canonicalIds_nodup (uv :: types)

/-- A type-hole insertion exposes IDs in ascending order. -/
theorem typePositions_hole_sorted (uv : Nat) (types : List Nat) :
    (typePositions true (.hole uv) types).Pairwise (· ≤ ·) := by
  rw [typePositions_hole_true]
  exact canonicalIds_sorted (uv :: types)

/-- Every child below a type position uses the same right-fold type traversal. -/
theorem typePositions_type_node (symbol : Symbol) (children : List (Fragment Symbol)) (types : List Nat) :
    typePositions true (.node symbol children) types = children.foldr (typePositions true) types := by
  simp [typePositions]

/-- Application types retain the nested annotation/marker and function/argument folds. -/
theorem typePositions_app (annotation marker function argument : Fragment Symbol) (types : List Nat) :
    typePositions false (.node ("app", FullSyntax.Formula.top) [annotation, marker, function, argument]) types =
      [annotation, marker].foldr (typePositions true)
        ([function, argument].foldr (typePositions false) types) := by
  simp [typePositions]

/-- A filter records its program before its annotation in the type-set fold. -/
theorem typePositions_filter (annotation term : Fragment Symbol) (types : List Nat) :
    typePositions false (.node ("filter", FullSyntax.Formula.top) [annotation, term]) types =
      typePositions true annotation (typePositions false term types) := by
  simp [typePositions]

/-- A complete type-position fragment contributes no program hole. -/
theorem programHoles_type (fragment : Fragment Symbol) : programHoles true fragment = [] := by
  cases fragment <;> simp [programHoles]

/-- A program-position hole retains its raw ID. -/
theorem programHoles_hole (uv : Nat) : programHoles false (.hole uv) = [uv] := rfl

/-- An application retains all function holes before all argument holes. -/
theorem programHoles_app (annotation marker function argument : Fragment Symbol) :
    programHoles false (.node ("app", FullSyntax.Formula.top) [annotation, marker, function, argument]) =
      programHoles false function ++ programHoles false argument := by
  simp [programHoles]

/-- Application membership is exactly function or argument program membership. -/
theorem programHoles_app_member (annotation marker function argument : Fragment Symbol) (uv : Nat) :
    uv ∈ programHoles false (.node ("app", FullSyntax.Formula.top) [annotation, marker, function, argument]) ↔
      uv ∈ programHoles false function ∨ uv ∈ programHoles false argument := by
  rw [programHoles_app, List.mem_append]

/-- A filter contributes only its program child's ordered holes. -/
theorem programHoles_filter (annotation term : Fragment Symbol) :
    programHoles false (.node ("filter", FullSyntax.Formula.top) [annotation, term]) =
      programHoles false term := by
  simp [programHoles]

/-- Two occurrences of the same program hole remain two occurrences. -/
theorem programHoles_repeated (annotation marker : Fragment Symbol) (uv : Nat) :
    programHoles false (.node ("app", FullSyntax.Formula.top) [annotation, marker, .hole uv, .hole uv]) =
      [uv, uv] := by
  rw [programHoles_app]
  rfl

/-- A nonordinary four-child label does not select program children. -/
theorem programHoles_other_four (symbol : Symbol) (annotation marker function argument : Fragment Symbol)
    (other : symbol ≠ ("app", FullSyntax.Formula.top)) :
    programHoles false (.node symbol [annotation, marker, function, argument]) = [] := by
  simp [programHoles, other]

/-- A type hole renders as the ordinary question marker, with no children. -/
theorem openProgram_type_hole (uv : Nat) (children : List SourcePruningTemplates.PartialTerm) :
    openProgram true (.node (.hole uv) children) = .node ("?", FullSyntax.Formula.top) [] := by
  simp [openProgram]

/-- A program hole renders its original nonnegative decimal ID. -/
theorem openProgram_program_hole (uv : Nat) (children : List SourcePruningTemplates.PartialTerm) :
    openProgram false (.node (.hole uv) children) =
      .node ("?program#" ++ toString uv, FullSyntax.Formula.top) [] := by
  simp [openProgram]

/-- Truncation uses the ordinary Mu marker at either position. -/
theorem openProgram_truncated (isType : Bool) (children : List SourcePruningTemplates.PartialTerm) :
    openProgram isType (.node .truncated children) = .node ("Mu", FullSyntax.Formula.top) [] := by
  simp [openProgram]

/-- Concrete labels and child order remain unchanged below a type position. -/
theorem openProgram_type_node (symbol : Symbol) (children : List SourcePruningTemplates.PartialTerm) :
    openProgram true (.node (.concrete symbol) children) =
      .node symbol (children.map (openProgram true)) := by
  simp [openProgram]

/-- An application renders annotation/marker as types and function/argument as programs. -/
theorem openProgram_app (annotation marker function argument : SourcePruningTemplates.PartialTerm) :
    openProgram false (.node (.concrete ("app", FullSyntax.Formula.top)) [annotation, marker, function, argument]) =
      .node ("app", FullSyntax.Formula.top)
        [openProgram true annotation, openProgram true marker,
          openProgram false function, openProgram false argument] := by
  simp [openProgram]

/-- A filter renders its first child as a type and its second child as a program. -/
theorem openProgram_filter (annotation term : SourcePruningTemplates.PartialTerm) :
    openProgram false (.node (.concrete ("filter", FullSyntax.Formula.top)) [annotation, term]) =
      .node ("filter", FullSyntax.Formula.top) [openProgram true annotation, openProgram false term] := by
  simp [openProgram]

/-- Other four-child labels retain all children as types, including refinements. -/
theorem openProgram_other_four (symbol : Symbol)
    (annotation marker function argument : SourcePruningTemplates.PartialTerm)
    (other : symbol ≠ ("app", FullSyntax.Formula.top)) :
    openProgram false (.node (.concrete symbol) [annotation, marker, function, argument]) =
      .node symbol ([annotation, marker, function, argument].map (openProgram true)) := by
  simp [openProgram, other]

end MicroCFTA.SourcePruningPositions
