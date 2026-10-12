import MicroCFTA.IntegerTermCodec

/-!
# Coordinate order in open applicative spines

The source joins function keys before argument keys. Its reader splits the
point after the variables of the function keys. Hole filling traverses the
same function term before the argument term. User maps can repeat values;
no inverse law for a user function is required here.
-/
namespace MicroCFTA.OpenIntegerReaders
open Language RecipeCompile

/-- The typed bare-spine cases whose source readers inspect integer coordinates. -/
inductive Reader : Type → Type 1 where
  | pure (value : α) : Reader α
  | integer : Reader Int
  | map (transform : α → β) (inner : Reader α) : Reader β
  | pay (inner : Reader α) : Reader α
  | app (functions : Reader (α → β)) (arguments : Reader α) : Reader β

/-- One key per spine operand; lifted values create no observation key. -/
def counts : Reader α → List Nat
  | .pure _ => []
  | .integer => [1]
  | .map _ inner | .pay inner => counts inner
  | .app functions arguments => counts functions ++ counts arguments

/-- The source openCount sum at each spine. -/
def width (reader : Reader α) : Nat := (counts reader).sum

/-- Private Pure and Apply tags do not consume integer coordinates. -/
def template : Reader α → Term (FillLabel Symbol)
  | .pure _ => .node (.internal 0) []
  | .integer => .node .placeholder []
  | .map _ inner | .pay inner => template inner
  | .app functions arguments => .node (.internal 1) [template functions, template arguments]

/-- Execute the source split order; an empty integer read remains an explicit failure. -/
def evaluate : Reader α → List Int → Option α
  | .pure value, _ => some value
  | .integer, point => point.head?
  | .map transform inner, point => (evaluate inner point).map transform
  | .pay inner, point => evaluate inner point
  | .app functions arguments, point => do
      let function ← evaluate functions (point.take (width functions))
      let argument ← evaluate arguments (point.drop (width functions))
      pure (function argument)

/-- Every generated placeholder is a leaf, including under arbitrary maps and products. -/
theorem template_valid (reader : Reader α) : IntegerTermCodec.LeafHoles (template (Symbol := Symbol) reader) := by
  induction reader with
  | pure value => simp [template, IntegerTermCodec.LeafHoles]
  | integer => simp [template, IntegerTermCodec.LeafHoles]
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments left right => simp [template, IntegerTermCodec.LeafHoles, left, right]

/-- The source key count equals the number of placeholders in the actual generated spine. -/
theorem template_holes (reader : Reader α) : holes (template (Symbol := Symbol) reader) = width reader := by
  induction reader with
  | pure value => simp [template, width, counts, holes, forestHoles]
  | integer => simp [template, width, counts, holes]
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments left right =>
      simp [template, width, counts, holes, forestHoles, left, right]

/-- Taking the source number of function-side keys gives exactly their coordinate count. -/
theorem source_split (functions : Reader (α → β)) (arguments : Reader α) :
    ((counts (.app functions arguments)).take (counts functions).length).sum = width functions := by
  simp [counts, width]

/-- The function term leaves exactly the coordinate suffix passed to the argument reader. -/
theorem fill_reader_split (literal : Int → Symbol) (specialize : List Int → Symbol → Symbol)
    (functions : Reader (α → β)) (arguments : Reader α) (point : List Int) :
    (fillTerm literal specialize point (template functions)).1 =
      point.drop (((counts (.app functions arguments)).take (counts functions).length).sum) := by
  rw [fillTerm_remaining, template_holes, source_split]

/-- Filling a generated spine and reading its placeholder labels recovers its complete point. -/
theorem fill_extract (literal : Int → Symbol) (specialize : List Int → Symbol → Symbol)
    (reader : Reader α) (point : List Int) (dimension : point.length = width reader) :
    IntegerTermCodec.holeSymbols (template reader) (fillTerm literal specialize point (template reader)).2 =
      some (point.map literal) :=
  IntegerTermCodec.exact_symbols literal specialize point (template reader) (template_valid reader)
    (dimension.trans (template_holes reader).symm)

/-- Every coordinate access of a well-sized generated reader succeeds. -/
theorem evaluate_total (reader : Reader α) (point : List Int) (dimension : point.length = width reader) :
    ∃ value, evaluate reader point = some value := by
  induction reader generalizing point with
  | pure value => exact ⟨value, rfl⟩
  | integer =>
      cases point with
      | nil => simp [width, counts] at dimension
      | cons value rest => exact ⟨value, rfl⟩
  | map transform inner ih =>
      obtain ⟨value, found⟩ := ih point dimension
      exact ⟨transform value, by simp [evaluate, found]⟩
  | pay inner ih => exact ih point dimension
  | app functions arguments left right =>
      have sizes : point.length = width functions + width arguments := by simpa [width, counts] using dimension
      obtain ⟨function, hf⟩ := left (point.take (width functions)) (by simp; omega)
      obtain ⟨argument, ha⟩ := right (point.drop (width functions)) (by simp; omega)
      exact ⟨function argument, by simp [evaluate, hf, ha]⟩

end MicroCFTA.OpenIntegerReaders
