import MicroCFTA.SourceCurrentOuterUntouchedProgress

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

#check @MicroCFTA.SourceCurrentOuterUntouchedProgress.walk_prefix
#print MicroCFTA.SourceCurrentOuterUntouchedProgress.walk_prefix
#print axioms MicroCFTA.SourceCurrentOuterUntouchedProgress.walk_prefix

#check @MicroCFTA.SourceCurrentOuterUntouchedProgress.dispatch
#print MicroCFTA.SourceCurrentOuterUntouchedProgress.dispatch
#print axioms MicroCFTA.SourceCurrentOuterUntouchedProgress.dispatch

#check @MicroCFTA.SourceCurrentOuterUntouchedProgress.budget
#print MicroCFTA.SourceCurrentOuterUntouchedProgress.budget
#print axioms MicroCFTA.SourceCurrentOuterUntouchedProgress.budget
