import MicroCFTA.SourceCurrentStoredLiveUnionLineage

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000


#check @MicroCFTA.SourceCurrentStoredLiveUnionLineage.union
#print MicroCFTA.SourceCurrentStoredLiveUnionLineage.union
#print axioms MicroCFTA.SourceCurrentStoredLiveUnionLineage.union

#check @MicroCFTA.SourceCurrentStoredLiveUnionLineage.binder_free
#print MicroCFTA.SourceCurrentStoredLiveUnionLineage.binder_free
#print axioms MicroCFTA.SourceCurrentStoredLiveUnionLineage.binder_free

#check @MicroCFTA.SourceCurrentStoredLiveUnionLineage.initial
#print MicroCFTA.SourceCurrentStoredLiveUnionLineage.initial
#print axioms MicroCFTA.SourceCurrentStoredLiveUnionLineage.initial
