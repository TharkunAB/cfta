import MicroCFTA.SourceCurrentStoredRootDeletionFilter

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentStoredRootDeletionFilter.singleton
#print MicroCFTA.SourceCurrentStoredRootDeletionFilter.singleton
#print axioms MicroCFTA.SourceCurrentStoredRootDeletionFilter.singleton

#check @MicroCFTA.SourceCurrentStoredRootDeletionFilter.filter_profile
#print MicroCFTA.SourceCurrentStoredRootDeletionFilter.filter_profile
#print axioms MicroCFTA.SourceCurrentStoredRootDeletionFilter.filter_profile
