import MicroCFTA.SourceCurrentHereditarySelection
import MicroCFTA.SourceCurrentHereditaryMergeStore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.SourceCurrentHereditarySelection.anyAccepts
#check @MicroCFTA.SourceCurrentHereditarySelection.anyAccepts
#print axioms MicroCFTA.SourceCurrentHereditarySelection.retain
#check @MicroCFTA.SourceCurrentHereditarySelection.retain
#print axioms MicroCFTA.SourceCurrentHereditarySelection.select
#check @MicroCFTA.SourceCurrentHereditarySelection.select
#print axioms MicroCFTA.SourceCurrentHereditaryMergeStore.Certified
#check @MicroCFTA.SourceCurrentHereditaryMergeStore.Certified
#print axioms MicroCFTA.SourceCurrentHereditaryMergeStore.run_store
#check @MicroCFTA.SourceCurrentHereditaryMergeStore.run_store
#print axioms MicroCFTA.SourceCurrentHereditaryMergeStore.call
#check @MicroCFTA.SourceCurrentHereditaryMergeStore.call
#print axioms MicroCFTA.SourceCurrentHereditaryMergeStore.cold
#check @MicroCFTA.SourceCurrentHereditaryMergeStore.cold
