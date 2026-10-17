import MicroCFTA.SourceCurrentStoredCallsReplay

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentStoredCallsReplay.correct
#print MicroCFTA.SourceCurrentStoredCallsReplay.correct
#print axioms MicroCFTA.SourceCurrentStoredCallsReplay.correct

#check @MicroCFTA.SourceCurrentStoredCallsReplay.replay
#print MicroCFTA.SourceCurrentStoredCallsReplay.replay
#print axioms MicroCFTA.SourceCurrentStoredCallsReplay.replay

#check @MicroCFTA.SourceCurrentStoredCallsReplay.same
#print MicroCFTA.SourceCurrentStoredCallsReplay.same
#print axioms MicroCFTA.SourceCurrentStoredCallsReplay.same

