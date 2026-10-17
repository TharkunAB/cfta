import MicroCFTA.HeightOrderControlled

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

#print axioms MicroCFTA.HeightOrderControlled.iterate
#check @MicroCFTA.HeightOrderControlled.iterate

#print axioms MicroCFTA.HeightOrderControlled.majorant
#check @MicroCFTA.HeightOrderControlled.majorant

#print axioms MicroCFTA.HeightOrderControlled.majorant_zero
#check @MicroCFTA.HeightOrderControlled.majorant_zero

#print axioms MicroCFTA.HeightOrderControlled.majorant_succ
#check @MicroCFTA.HeightOrderControlled.majorant_succ

#print axioms MicroCFTA.HeightOrderControlled.majorant_ge
#check @MicroCFTA.HeightOrderControlled.majorant_ge

#print axioms MicroCFTA.HeightOrderControlled.majorant_mono
#check @MicroCFTA.HeightOrderControlled.majorant_mono

#print axioms MicroCFTA.HeightOrderControlled.Path
#check @MicroCFTA.HeightOrderControlled.Path

#print axioms MicroCFTA.HeightOrderControlled.Path.initial_bound
#check @MicroCFTA.HeightOrderControlled.Path.initial_bound

#print axioms MicroCFTA.HeightOrderControlled.Path.elapsed_le
#check @MicroCFTA.HeightOrderControlled.Path.elapsed_le

#print axioms MicroCFTA.HeightOrderControlled.Path.final_le
#check @MicroCFTA.HeightOrderControlled.Path.final_le

#print axioms MicroCFTA.HeightOrderControlled.Path.length_le
#check @MicroCFTA.HeightOrderControlled.Path.length_le
