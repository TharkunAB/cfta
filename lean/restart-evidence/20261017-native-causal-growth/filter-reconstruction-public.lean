import MicroCFTA.SourceCurrentStoredFilterReconstruction

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentStoredFilterReconstruction.retained
#print MicroCFTA.SourceCurrentStoredFilterReconstruction.retained
#print axioms MicroCFTA.SourceCurrentStoredFilterReconstruction.retained

#check @MicroCFTA.SourceCurrentStoredFilterReconstruction.complete
#print MicroCFTA.SourceCurrentStoredFilterReconstruction.complete
#print axioms MicroCFTA.SourceCurrentStoredFilterReconstruction.complete
