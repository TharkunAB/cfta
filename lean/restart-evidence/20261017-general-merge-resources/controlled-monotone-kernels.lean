import MicroCFTA.HeightOrderControlledMonotone
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.ControlledMonotoneChecks
open HeightOrderControlled

/-- The lower dimension is retained while the next dimension permits growth. -/
theorem two_dimensions :
    majorant Nat.succ 1 2 = 5 ∧ majorant Nat.succ 2 2 = 30 := by decide

/-- Increasing dimension and initial control retains the evaluated earlier envelope. -/
theorem joint_increase : majorant Nat.succ 1 2 ≤ majorant Nat.succ 2 3 := by
  exact majorant_joint_mono Nat.succ (fun enough => Nat.succ_le_succ enough)
    Nat.lt_succ_self (by decide) (by decide)

end MicroCFTA.ControlledMonotoneChecks

#print axioms MicroCFTA.ControlledMonotoneChecks.two_dimensions
#check @MicroCFTA.ControlledMonotoneChecks.two_dimensions
#print axioms MicroCFTA.ControlledMonotoneChecks.joint_increase
#check @MicroCFTA.ControlledMonotoneChecks.joint_increase
