import MicroCFTA.HeightOrderControlled
import MicroCFTA.SourceCurrentAllocatedReaderControl

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.HeightOrderControlled.majorant
#check @MicroCFTA.HeightOrderControlled.majorant

#print axioms MicroCFTA.HeightOrderControlled.Path.final_le
#check @MicroCFTA.HeightOrderControlled.Path.final_le

#print axioms MicroCFTA.HeightOrderControlled.Path.length_le
#check @MicroCFTA.HeightOrderControlled.Path.length_le

#print axioms MicroCFTA.HeightOrderControlled.Path.elapsed_le
#check @MicroCFTA.HeightOrderControlled.Path.elapsed_le

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.good
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.good

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.fits
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.fits

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.decreases
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.decreases
