import MicroCFTA.SourceCurrentConstrainedCapEditForecast
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.EditForecastKernels
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
local notation "operands" => SourceEqualityClassTarget.operandPaths
private theorem power_large (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.add_assoc, Nat.pow_succ]
      omega

private theorem exists_room (p : SourceCurrentAllocatedNativeResourceSourceCurrentConstrainedCapEditForecast.Profile) :
    ∃ bits, SourceCurrentAllocatedNativeResourceSourceCurrentConstrainedCapEditForecast.Room bits p := by
  let total := p.nodes + p.edges + p.domains + 2 ^ (p.nodes + p.nodes * p.nodes)
  refine ⟨total + 1, ?_⟩
  have large := power_large total
  have one := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 1 by omega)
  have two := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 2 by omega)
  change p.nodes < 2 ^ (total + 1) ∧ p.edges ≤ 2 ^ (total + 1 + 2) ∧
    p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) < 2 ^ (total + 1 + 1)
  have nodes : p.nodes ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right p.nodes p.edges)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have edges : p.edges ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_left p.edges p.nodes)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have domains : p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) ≤ total :=
    Nat.add_le_add_right (Nat.le_add_left p.domains (p.nodes + p.edges)) _
  exact ⟨Nat.lt_of_le_of_lt nodes large,
    Nat.le_trans edges (Nat.le_trans (Nat.le_of_lt large) two),
    Nat.lt_of_le_of_lt domains (Nat.lt_of_lt_of_le large one)⟩


/-- One finite initial room supports every original token at either slot branch. -/
theorem all_tokens_initial (record : SourceEqualityClassOrder.Record) (count level : Nat) (profile : Profile) :
    ∃ bits, Room bits (SourceCurrentConstrainedCapEditForecast.planProfile record count level profile) ∧
      ∀ path ∈ record.paths, ∀ found,
        SourceCurrentConstrainedCapSharedForecast.LeafReserved bits count (operands record.paths path) found profile ∧
        Le (SourceCurrentConstrainedCapSharedForecast.leafProfile count (operands record.paths path) found profile)
          (SourceCurrentConstrainedCapEditForecast.planProfile record count level profile) ∧
        SourceCurrentConstrainedCapSharedForecast.leafFuel count (operands record.paths path) found profile ≤
          SourceCurrentConstrainedCapEditForecast.stageFuel record count (SourceCurrentConstrainedCapEditForecast.planProfile record count level profile) := by
  obtain ⟨bits, room⟩ := exists_room (SourceCurrentConstrainedCapEditForecast.planProfile record count level profile)
  refine ⟨bits, room, ?_⟩
  intro path member found
  have stage := SourceCurrentConstrainedCapEditForecast.plan_stage record count level profile
  exact ⟨SourceCurrentConstrainedCapEditForecast.stage_leaf_reserved record count bits path found (Le.refl profile) member (room.mono stage),
    (SourceCurrentConstrainedCapEditForecast.stage_leaf_profile record count path found profile member).trans stage,
    Nat.le_trans (SourceCurrentConstrainedCapEditForecast.stage_leaf_fuel record count path found profile member)
      (SourceCurrentConstrainedCapEditForecast.stageFuel_mono record count (SourceCurrentConstrainedCapEditForecast.plan_ge record count level profile))⟩

/-- A scheduled child uses the common final room and fuel without a later room premise. -/
theorem child_tokens_initial (record : SourceEqualityClassOrder.Record) (count level : Nat) (profile : Profile)
    (row child : Nat) (rowInside : row < SourceCurrentConstrainedCapEditForecast.scalar (SourceCurrentConstrainedCapEditForecast.stageProfile record count profile))
    (childInside : child < SourceCurrentConstrainedCapEditForecast.scalar (SourceCurrentConstrainedCapEditForecast.stageProfile record count profile)) :
    let entry := SourceCurrentConstrainedCapEditForecast.scan (SourceCurrentConstrainedCapEditForecast.planProfile record count level) child
      (SourceCurrentConstrainedCapEditForecast.scan (SourceCurrentConstrainedCapEditForecast.rowStep record count level (SourceCurrentConstrainedCapEditForecast.scalar (SourceCurrentConstrainedCapEditForecast.stageProfile record count profile)))
        row (SourceCurrentConstrainedCapEditForecast.stageProfile record count profile))
    let final := SourceCurrentConstrainedCapEditForecast.planProfile record count (level + 1) profile
    ∃ bits, Room bits final ∧
      Le (SourceCurrentConstrainedCapEditForecast.stageProfile record count entry) final ∧
      ∀ path ∈ record.paths, ∀ found,
        SourceCurrentConstrainedCapSharedForecast.LeafReserved bits count (operands record.paths path) found entry ∧
        Le (SourceCurrentConstrainedCapSharedForecast.leafProfile count (operands record.paths path) found entry) final ∧
        SourceCurrentConstrainedCapSharedForecast.leafFuel count (operands record.paths path) found entry ≤ SourceCurrentConstrainedCapEditForecast.stageFuel record count final := by
  dsimp only
  let entry := SourceCurrentConstrainedCapEditForecast.scan (SourceCurrentConstrainedCapEditForecast.planProfile record count level) child
    (SourceCurrentConstrainedCapEditForecast.scan (SourceCurrentConstrainedCapEditForecast.rowStep record count level (SourceCurrentConstrainedCapEditForecast.scalar (SourceCurrentConstrainedCapEditForecast.stageProfile record count profile)))
      row (SourceCurrentConstrainedCapEditForecast.stageProfile record count profile))
  let final := SourceCurrentConstrainedCapEditForecast.planProfile record count (level + 1) profile
  obtain ⟨bits, room⟩ := exists_room final
  have stage : Le (SourceCurrentConstrainedCapEditForecast.stageProfile record count entry) final :=
    (SourceCurrentConstrainedCapEditForecast.plan_stage record count level entry).trans
      (SourceCurrentConstrainedCapEditForecast.plan_child_return record count level profile rowInside childInside)
  have entryBound : Le entry final := (SourceCurrentConstrainedCapEditForecast.stage_ge record count entry).trans stage
  refine ⟨bits, room, stage, ?_⟩
  intro path member found
  exact ⟨SourceCurrentConstrainedCapEditForecast.stage_leaf_reserved record count bits path found (Le.refl entry) member (room.mono stage),
    (SourceCurrentConstrainedCapEditForecast.stage_leaf_profile record count path found entry member).trans stage,
    Nat.le_trans (SourceCurrentConstrainedCapEditForecast.stage_leaf_fuel record count path found entry member)
      (SourceCurrentConstrainedCapEditForecast.stageFuel_mono record count entryBound)⟩
end MicroCFTA.EditForecastKernels

#print axioms MicroCFTA.EditForecastKernels.all_tokens_initial
#check @MicroCFTA.EditForecastKernels.all_tokens_initial
#print axioms MicroCFTA.EditForecastKernels.child_tokens_initial
#check @MicroCFTA.EditForecastKernels.child_tokens_initial
