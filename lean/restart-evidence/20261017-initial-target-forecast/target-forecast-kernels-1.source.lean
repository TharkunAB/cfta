import MicroCFTA.SourceCurrentConstrainedCapTargetForecast

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.TargetForecastIntegration
open SourceCurrentConstrainedCapTargetForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
local notation "Query" => SourceCurrentAllocatedNativeResourceForecast.step

/-- An empty literal Target retains a concrete initial profile and uses zero fuel. -/
theorem empty_target (bits : Nat) :
    scalar ⟨2, 3, 4, 5⟩ = 5 ∧ targetProfile 7 [] ⟨2, 3, 4, 5⟩ = ⟨2, 3, 4, 5⟩ ∧
      targetFuel 7 [] ⟨2, 3, 4, 5⟩ = 0 ∧ TargetReserved bits 7 [] ⟨2, 3, 4, 5⟩ :=
  ⟨rfl, rfl, rfl, trivial⟩

/-- Three original paths forecast their three Operands before the two native queries in exact Fold order. -/
theorem ordered_three_paths (bits count : Nat) (seed first second : List Int) (profile : Profile)
    (reserved : Reserved bits count seed [first, second] profile) :
    let one := operand first count profile
    let two := operand second count one
    let base := operand seed count two
    targetProfile count [seed, first, second] profile = Query (Query base) ∧
      Le profile one ∧ Le one two ∧ Le two base ∧ Le base (Query base) ∧ Le (Query base) (Query (Query base)) ∧
      Reserved bits count seed [second] one ∧ Room bits base ∧ Room bits (Query base) := by
  exact ⟨rfl, operand_ge first count profile, operand_ge second count _, operand_ge seed count _,
    SourceCurrentAllocatedNativeResourceForecast.step_ge _, SourceCurrentAllocatedNativeResourceForecast.step_ge _,
    reserved.tail, reserved.tail.query, reserved.query⟩

/-- The same shared Target fuel covers every Operand and both queries at their own scheduled profiles. -/
theorem three_path_fuels (count : Nat) (seed first second : List Int) (profile : Profile) :
    let one := operand first count profile
    let two := operand second count one
    let base := operand seed count two
    let fuel := targetFuel count [seed, first, second] profile
    operandFuel first count profile ≤ fuel ∧ operandFuel second count one ≤ fuel ∧
      operandFuel seed count two ≤ fuel ∧ queryFuel base ≤ fuel ∧ queryFuel (Query base) ≤ fuel := by
  have remaining := foldFuel_tail count seed first [second] profile
  exact ⟨foldFuel_head count seed first [second] profile,
    Nat.le_trans (foldFuel_head count seed second [] _) remaining,
    Nat.le_trans (foldFuel_tail count seed second [] _) remaining,
    Nat.le_trans (foldFuel_query count seed second [] _) remaining,
    foldFuel_query count seed first [second] profile⟩

#print axioms empty_target
#check @empty_target
#print axioms ordered_three_paths
#check @ordered_three_paths
#print axioms three_path_fuels
#check @three_path_fuels
end MicroCFTA.TargetForecastIntegration
