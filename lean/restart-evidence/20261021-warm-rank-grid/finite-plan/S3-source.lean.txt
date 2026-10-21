import MicroCFTA.SourceCurrentOuterInitialSchedule
import MicroCFTA.SourceCurrentOuterCopiedWarmHit

/-!
# Initial lower-fuel ceilings for the outer phases

The six recurrences use the exact predicted entries of the physical
schedule. Each Parent contributes its common nine-stage fuel ceiling.
Raw reconstruction and inherited operations consume no lower-worker fuel.
No monotonicity in the profile or guard alphabet is assumed.
-/
namespace MicroCFTA.SourceCurrentOuterInitialFuel
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentOuterCopiedWarmHit (Phase)
namespace Schedule
export SourceCurrentOuterInitialSchedule (parent node descendants)
end Schedule
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Seed" => List Guard × Profile

/-- One predicted Parent contributes the common bound for each of its nine lower fuels. -/
noncomputable def parentNeed (budget : Nat) (seed : Seed) : Nat :=
  SourceCurrentParentUniformEnvelope.fuel budget seed.1 seed.2

mutual
/-- Node demand reserves its possible body; ready hits consume no lower fuel. -/
noncomputable def nodeNeed (fuel budget : Nat) (seed : Seed) : Nat :=
  bodyNeed fuel budget seed
termination_by (fuel, 3)

/-- A nonterminal ordinary body reserves its row pass. -/
noncomputable def bodyNeed (fuel budget : Nat) (seed : Seed) : Nat :=
  match fuel with
  | 0 => 0
  | next + 1 => rowsNeed next budget seed
termination_by (fuel, 2)

/-- Row work reserves Parent, descendants and the suffix at their exact predicted entries. -/
noncomputable def rowsNeed (fuel budget : Nat) (seed : Seed) : Nat :=
  match fuel with
  | 0 => 0
  | next + 1 => max (parentNeed budget seed)
      (max (descendantsNeed next budget (Schedule.parent budget seed))
        (rowsNeed next budget (Schedule.descendants next budget (Schedule.parent budget seed))))
termination_by (fuel, 2)

/-- Descendants reserve children; their final raw constructor consumes no lower fuel. -/
noncomputable def descendantsNeed (fuel budget : Nat) (seed : Seed) : Nat :=
  childrenNeed fuel budget seed
termination_by (fuel, 2)

/-- A live combined field reserves its indexed walk; contradiction consumes no lower fuel. -/
noncomputable def childrenNeed (fuel budget : Nat) (seed : Seed) : Nat :=
  walkNeed fuel budget seed
termination_by (fuel, 1)

/-- Each walk slot reserves its node and its suffix at the predicted node return. -/
noncomputable def walkNeed (fuel budget : Nat) (seed : Seed) : Nat :=
  match fuel with
  | 0 => 0
  | next + 1 => max (nodeNeed next budget seed)
      (walkNeed next budget (Schedule.node next budget seed))
termination_by (fuel, 0)
end

/-- The literal phase tag selects the corresponding initial lower-fuel bound. -/
noncomputable def phaseNeed (budget : Nat) (phase : Phase width) (seed : Seed) : Nat :=
  match phase with
  | .node fuel _ _ => nodeNeed fuel budget seed
  | .body fuel _ _ => bodyNeed fuel budget seed
  | .rows fuel _ _ _ => rowsNeed fuel budget seed
  | .descendants fuel _ _ _ => descendantsNeed fuel budget seed
  | .children fuel _ _ _ => childrenNeed fuel budget seed
  | .walk fuel _ _ _ _ => walkNeed fuel budget seed

/-- The initial row ceiling includes its first Parent at the original seed. -/
theorem rows_parent_le (fuel budget : Nat) (seed : Seed) :
    parentNeed budget seed ≤ rowsNeed (fuel + 1) budget seed := by
  conv => rhs; rw [rowsNeed]
  exact Nat.le_max_left _ _

/-- The initial row ceiling includes descendants at the predicted Parent return. -/
theorem rows_descendants_le (fuel budget : Nat) (seed : Seed) :
    descendantsNeed fuel budget (Schedule.parent budget seed) ≤ rowsNeed (fuel + 1) budget seed := by
  conv => rhs; rw [rowsNeed]
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The initial row ceiling includes its suffix at the predicted descendant return. -/
theorem rows_tail_le (fuel budget : Nat) (seed : Seed) :
    rowsNeed fuel budget (Schedule.descendants fuel budget (Schedule.parent budget seed)) ≤
      rowsNeed (fuel + 1) budget seed := by
  conv => rhs; rw [rowsNeed]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- The initial walk ceiling includes its next node at the original seed. -/
theorem walk_node_le (fuel budget : Nat) (seed : Seed) :
    nodeNeed fuel budget seed ≤ walkNeed (fuel + 1) budget seed := by
  conv => rhs; rw [walkNeed]
  exact Nat.le_max_left _ _

/-- The initial walk ceiling includes its suffix at the predicted node return. -/
theorem walk_tail_le (fuel budget : Nat) (seed : Seed) :
    walkNeed fuel budget (Schedule.node fuel budget seed) ≤ walkNeed (fuel + 1) budget seed := by
  conv => rhs; rw [walkNeed]
  exact Nat.le_max_right _ _

/-- One row-bound test is equivalent to the three exact following phase tests. -/
theorem rows_split (fuel budget : Nat) (seed : Seed) (ceiling : Nat) :
    rowsNeed (fuel + 1) budget seed ≤ ceiling ↔
      parentNeed budget seed ≤ ceiling ∧
      descendantsNeed fuel budget (Schedule.parent budget seed) ≤ ceiling ∧
      rowsNeed fuel budget (Schedule.descendants fuel budget (Schedule.parent budget seed)) ≤ ceiling := by
  conv => lhs; rw [rowsNeed]
  simp only [Nat.max_le]

/-- One walk-bound test is equivalent to its node and exact suffix tests. -/
theorem walk_split (fuel budget : Nat) (seed : Seed) (ceiling : Nat) :
    walkNeed (fuel + 1) budget seed ≤ ceiling ↔
      nodeNeed fuel budget seed ≤ ceiling ∧
      walkNeed fuel budget (Schedule.node fuel budget seed) ≤ ceiling := by
  conv => lhs; rw [walkNeed]
  exact Nat.max_le

end MicroCFTA.SourceCurrentOuterInitialFuel
