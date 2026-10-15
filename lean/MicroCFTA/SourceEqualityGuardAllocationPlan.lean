import MicroCFTA.SourceCompactGuards

/-!
# Delayed positive-guard equality constructors

The Maybe constructor test does not force its equality payload. A successful
test retains the original Same constructors and right-fold combination tree.
Unsupported syntax returns no plan. No constraint cache is accessed here.
Demand and allocation receipts are separate from this pure syntax traversal.
-/
namespace MicroCFTA.SourceEqualityGuardAllocationPlan
open SourceGuards

/-- A delayed source equality payload retains each normalization and combination constructor. -/
inductive Plan where
  | empty
  | pair (left right : Path)
  | combine (first second : Plan)

/-- Read the exact source payload if the delayed constructor is demanded to completion. -/
noncomputable def Plan.classes : Plan → Option EqualityNormalize.Constraints
  | .empty => some []
  | .pair left right => SourceCompactGuards.normalize [[left, right]]
  | .combine first second => SourceCompactGuards.combineEqualities first.classes second.classes

mutual
  /-- Test positive syntax without forcing any constructed equality payload. -/
  def make : Guard Formula → Option Plan
    | .top => some .empty
    | .same left right => if left ≠ right then some (.pair left right) else none
    | .and parts => makeList parts
    | _ => none

  /-- Retain the literal source right fold, including its final live empty value. -/
  def makeList : List (Guard Formula) → Option Plan
    | [] => some .empty
    | first :: rest => do
        let head ← make first
        let tail ← makeList rest
        pure (.combine head tail)
end

mutual
  /-- Delayed positive extraction retains the exact normalized source payload, including failure. -/
  theorem make_exact (guard : Guard Formula) :
      (make guard).map Plan.classes = SourceCompactGuards.positiveNormalized guard := by
    cases guard with
    | top => rfl
    | same left right =>
        by_cases different : left ≠ right <;> simp [make, SourceCompactGuards.positiveNormalized, different, Plan.classes]
    | and parts => exact makeList_exact parts
    | bottom | entails _ _ | satisfies _ _ | holds _ _ | substitute _ _ | not _ | or _ => rfl

  /-- The delayed conjunction tree retains every source intermediate combination in its original argument order. -/
  theorem makeList_exact (guards : List (Guard Formula)) :
      (makeList guards).map Plan.classes = SourceCompactGuards.positiveNormalizedList guards := by
    cases guards with
    | nil => rfl
    | cons first rest =>
        rw [SourceCompactGuards.positiveNormalizedList, ← make_exact first, ← makeList_exact rest]
        cases head : make first <;> cases tail : makeList rest <;> simp [makeList, head, tail, Plan.classes]
end

end MicroCFTA.SourceEqualityGuardAllocationPlan
