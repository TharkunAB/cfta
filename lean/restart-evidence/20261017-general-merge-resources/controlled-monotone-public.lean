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

#print axioms MicroCFTA.HeightOrderControlled.majorant_dimension_succ
#check @MicroCFTA.HeightOrderControlled.majorant_dimension_succ

#print axioms MicroCFTA.HeightOrderControlled.majorant_dimension_mono
#check @MicroCFTA.HeightOrderControlled.majorant_dimension_mono

#print axioms MicroCFTA.HeightOrderControlled.majorant_joint_mono
#check @MicroCFTA.HeightOrderControlled.majorant_joint_mono

#print axioms MicroCFTA.HeightOrderControlled.majorant_diagonal_mono
#check @MicroCFTA.HeightOrderControlled.majorant_diagonal_mono
