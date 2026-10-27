import MicroCFTA.EnumerationCPSChecked

/-!
# Ordered enumeration results across different state representations

Successful values are equal and returned states are related. Errors keep their
identity and position. The bind law uses explicit finite rows. It does not infer
continuation behavior from one observation of an arbitrary CPS computation.
-/

namespace MicroCFTA.EnumerationResultRelation

variable {Left Right Error α β : Type}

/-- Relate one successful state transition or one unchanged explicit error. -/
inductive Outcome (relation : Left → Right → Prop) :
    Except Error (α × Left) → Except Error (α × Right) → Prop where
  /-- The same error occupies both result positions. -/
  | error (error : Error) : Outcome relation (.error error) (.error error)
  /-- Equal values have related final states. -/
  | ok (value : α) (states : relation left right) :
      Outcome relation (.ok (value, left)) (.ok (value, right))

/-- Relate every result at the same position in both finite lists. -/
abbrev Results (relation : Left → Right → Prop)
    (left : List (Except Error (α × Left))) (right : List (Except Error (α × Right))) : Prop :=
  Language.All₂ (Outcome relation) left right

/-- Ordered alternatives preserve the relation when concatenated. -/
theorem append (first : Results relation left right) (rest : Results relation later tail) :
    Results relation (left ++ later) (right ++ tail) := by
  induction first with
  | nil => exact rest
  | cons head _ ih => exact .cons head ih

/-- Related result lists have the same number of successes and errors together. -/
theorem length_eq (related : Results relation left right) : left.length = right.length :=
  Language.All₂.length_eq related

/-- Bind preserves every result and error position through related continuations. -/
theorem bind_rows
    (first : EnumerationCPSChecked.Rows Left Error α)
    (second : EnumerationCPSChecked.Rows Right Error α)
    (leftNext : α → EnumerationCPSChecked.Rows Left Error β)
    (rightNext : α → EnumerationCPSChecked.Rows Right Error β)
    (initial : Results relation (first left) (second right))
    (following : ∀ value left right, relation left right →
      Results relation (leftNext value left) (rightNext value right)) :
    Results relation (EnumerationCPSChecked.bindRows first leftNext left)
      (EnumerationCPSChecked.bindRows second rightNext right) := by
  unfold EnumerationCPSChecked.bindRows
  induction initial with
  | nil => exact .nil
  | cons head _ ih =>
    simp only [List.flatMap_cons]
    cases head with
    | error error => exact .cons (.error error) ih
    | ok value states => exact append (following value _ _ states) ih

/-- Exact CPS representations transfer an ordered row relation to observations. -/
theorem represented
    (leftAction : EnumerationCPSChecked.Computation Left Error α)
    (rightAction : EnumerationCPSChecked.Computation Right Error α)
    (first : EnumerationCPSChecked.Rows Left Error α)
    (second : EnumerationCPSChecked.Rows Right Error α)
    (leftExact : EnumerationCPSChecked.Represents leftAction first)
    (rightExact : EnumerationCPSChecked.Represents rightAction second)
    (related : Results relation (first left) (second right)) :
    Results relation (EnumerationCPSChecked.allResults leftAction left)
      (EnumerationCPSChecked.allResults rightAction right) := by
  rw [EnumerationCPSChecked.allResults_exact leftAction first leftExact,
    EnumerationCPSChecked.allResults_exact rightAction second rightExact]
  exact related

end MicroCFTA.EnumerationResultRelation
