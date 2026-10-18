import MicroCFTA.SourceCurrentStoredMuProfileContract
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentStoredMuProfileContract.shadow
#print MicroCFTA.SourceCurrentStoredMuProfileContract.shadow
#print axioms MicroCFTA.SourceCurrentStoredMuProfileContract.shadow
#check @MicroCFTA.SourceCurrentStoredMuProfileContract.Correct
#print MicroCFTA.SourceCurrentStoredMuProfileContract.Correct
#print axioms MicroCFTA.SourceCurrentStoredMuProfileContract.Correct
#check @MicroCFTA.SourceCurrentStoredMuProfileContract.execute
#print MicroCFTA.SourceCurrentStoredMuProfileContract.execute
#print axioms MicroCFTA.SourceCurrentStoredMuProfileContract.execute
