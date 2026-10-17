import MicroCFTA.SourceCurrentTargetNumeric

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentTargetNumeric.fold_complete
#print axioms MicroCFTA.SourceCurrentTargetNumeric.fold_complete
#print MicroCFTA.SourceCurrentTargetNumeric.fold_complete

#check @MicroCFTA.SourceCurrentTargetNumeric.complete
#print axioms MicroCFTA.SourceCurrentTargetNumeric.complete
#print MicroCFTA.SourceCurrentTargetNumeric.complete

