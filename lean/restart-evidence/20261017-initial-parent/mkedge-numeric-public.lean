import MicroCFTA.SourceCurrentMkEdgeNumeric
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile
#print axioms MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile
#print MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile

#check @MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile_ge
#print axioms MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile_ge
#print MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile_ge

#check @MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile_mono
#print axioms MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile_mono
#print MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile_mono

#check @MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile_count_mono
#print axioms MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile_count_mono
#print MicroCFTA.SourceCurrentMkEdgeNumeric.finalProfile_count_mono

#check @MicroCFTA.SourceCurrentMkEdgeNumeric.complete
#print axioms MicroCFTA.SourceCurrentMkEdgeNumeric.complete
#print MicroCFTA.SourceCurrentMkEdgeNumeric.complete

#check @MicroCFTA.SourceCurrentMkEdgeNumeric.reject
#print axioms MicroCFTA.SourceCurrentMkEdgeNumeric.reject
#print MicroCFTA.SourceCurrentMkEdgeNumeric.reject
