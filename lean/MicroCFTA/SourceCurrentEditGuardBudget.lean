import MicroCFTA.SourceCurrentEditGuardAlphabet
import MicroCFTA.SourceCurrentConstrainedCapEditForecast

/-!
# Uniform finite guard counts for shared edit leaves

The shared worker fuel bounds its predicted Target and Leaf extensions.
One final stage ceiling therefore bounds every original path and slot
branch. The bound retains the complete original record syntax.
-/
namespace MicroCFTA.SourceCurrentEditGuardBudget
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
local notation "foldCount" => SourceCurrentTargetGuardAlphabet.foldCount
local notation "targetCount" => SourceCurrentTargetGuardAlphabet.targetCount
local notation "foldFuel" => SourceCurrentConstrainedCapTargetForecast.foldFuel
local notation "targetFuel" => SourceCurrentConstrainedCapTargetForecast.targetFuel
local notation "forceCount" => SourceCurrentEditGuardAlphabet.forceCount
local notation "leafCount" => SourceCurrentEditGuardAlphabet.leafCount
local notation "forceFuel" => SourceCurrentConstrainedCapSharedForecast.forceFuel
local notation "leafFuel" => SourceCurrentConstrainedCapSharedForecast.leafFuel
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound

/-- Every predicted Fold extension fits its path count times its shared fuel ceiling. -/
theorem fold_le_fuel (count : Nat) (seed : List Int) (paths : List (List Int)) (profile : Profile) :
    foldCount count seed paths profile ≤ (paths.length + 1) * (foldFuel count seed paths profile + 1) := by
  induction paths generalizing profile with
  | nil => simp only [SourceCurrentTargetGuardAlphabet.foldCount, List.length_nil, Nat.zero_add, Nat.one_mul]; omega
  | cons path paths ih =>
      let entry := SourceCurrentConstrainedCapTargetForecast.operand path count profile
      let query := SourceCurrentConstrainedCapTargetForecast.foldProfile count seed paths entry
      let fuel := foldFuel count seed (path :: paths) profile
      have tailFuel := SourceCurrentConstrainedCapTargetForecast.foldFuel_tail count seed path paths profile
      have tail : foldCount count seed paths entry ≤ (paths.length + 1) * (fuel + 1) := Nat.le_trans (ih entry)
        (Nat.mul_le_mul (Nat.le_refl (paths.length + 1)) (Nat.succ_le_succ tailFuel))
      have queryFuel := SourceCurrentConstrainedCapTargetForecast.foldFuel_query count seed path paths profile
      have steps : instructionBound query.nodes query.edges query.mass ≤ fuel := by
        change instructionBound query.nodes query.edges query.mass + 1 ≤ fuel at queryFuel
        omega
      change 1 + foldCount count seed paths entry + instructionBound query.nodes query.edges query.mass ≤
        (paths.length + 1 + 1) * (fuel + 1)
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left tail 1) steps) (by omega)

/-- An empty Target contributes no extensions and a nonempty Target uses its Fold bound. -/
theorem target_le_fuel (count : Nat) (paths : List (List Int)) (profile : Profile) :
    targetCount count paths profile ≤ paths.length * (targetFuel count paths profile + 1) := by
  cases paths with
  | nil => exact Nat.le_refl 0
  | cons seed paths => exact fold_le_fuel count seed paths profile

/-- Both target-slot branches have one common path and fuel bound. -/
theorem force_le_fuel (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) :
    forceCount count paths found profile ≤ paths.length * (forceFuel count paths found profile + 1) := by
  cases found with
  | false => exact target_le_fuel count paths profile
  | true => exact Nat.zero_le _

/-- The post-Force native query adds at most one more shared fuel block. -/
theorem leaf_le_fuel (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) :
    leafCount count paths found profile ≤ (paths.length + 1) * (leafFuel count paths found profile + 1) := by
  have first : forceCount count paths found profile ≤ paths.length * (leafFuel count paths found profile + 1) :=
    Nat.le_trans (force_le_fuel count paths found profile)
    (Nat.mul_le_mul (Nat.le_refl paths.length) (Nat.succ_le_succ
      (SourceCurrentConstrainedCapSharedForecast.leafFuel_force count paths found profile)))
  have last := SourceCurrentConstrainedCapSharedForecast.leafFuel_query count paths found profile
  unfold SourceCurrentConstrainedCapTargetForecast.queryFuel at last
  dsimp only [SourceCurrentEditGuardAlphabet.leafCount]
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.le_trans (Nat.add_le_add first (Nat.le_of_succ_le last)) (by omega)

/-- One pure stage ceiling bounds every original path and both target-slot branches. -/
def leafBound (record : SourceEqualityClassOrder.Record) (count : Nat) (ceiling : Profile) : Nat :=
  (record.paths.length + 1) * (SourceCurrentConstrainedCapEditForecast.stageFuel record count ceiling + 1)

/-- Initial profile inclusion identifies each literal Leaf count below the uniform bound. -/
theorem leaf_le_stage (record : SourceEqualityClassOrder.Record) (count : Nat)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (found : Bool)
    (profile ceiling : Profile) (bounded : Le profile ceiling) :
    leafCount count (SourceEqualityClassTarget.operandPaths record.paths path) found profile ≤
      leafBound record count ceiling := by
  have length : (SourceEqualityClassTarget.operandPaths record.paths path).length ≤ record.paths.length := by
    simp only [SourceEqualityClassTarget.operandPaths, List.length_map]
    exact List.length_filter_le _ _
  have fuel := Nat.le_trans (SourceCurrentConstrainedCapEditForecast.stage_leaf_fuel record count path found profile member)
    (SourceCurrentConstrainedCapEditForecast.stageFuel_mono record count bounded)
  exact Nat.le_trans (leaf_le_fuel count _ found profile)
    (Nat.mul_le_mul (Nat.succ_le_succ length) (Nat.succ_le_succ fuel))

/-- A fixed numeric ceiling bounds both row and child scans at every syntax level. -/
def nodeBound (record : SourceEqualityClassOrder.Record) (count : Nat) (ceiling : Profile) : Nat → Nat
  | 0 => 0
  | level + 1 => leafBound record count ceiling +
      SourceCurrentConstrainedCapEditForecast.scalar ceiling *
        (SourceCurrentConstrainedCapEditForecast.scalar ceiling * nodeBound record count ceiling level)

/-- Each positive syntax level includes the complete uniform Leaf bound. -/
theorem node_leaf (record : SourceEqualityClassOrder.Record) (count : Nat) (ceiling : Profile) (level : Nat) :
    leafBound record count ceiling ≤ nodeBound record count ceiling (level + 1) := Nat.le_add_right _ _

/-- Every pair of bounded ordered scan widths fits the next syntax-level bound. -/
theorem node_rows (record : SourceEqualityClassOrder.Record) (count : Nat) (ceiling : Profile) (level : Nat)
    (rows children : Nat) (rowBound : rows ≤ SourceCurrentConstrainedCapEditForecast.scalar ceiling)
    (childBound : children ≤ SourceCurrentConstrainedCapEditForecast.scalar ceiling) :
    rows * (children * nodeBound record count ceiling level) ≤ nodeBound record count ceiling (level + 1) :=
  Nat.le_trans (Nat.mul_le_mul rowBound (Nat.mul_le_mul childBound (Nat.le_refl _))) (Nat.le_add_left _ _)

end MicroCFTA.SourceCurrentEditGuardBudget
