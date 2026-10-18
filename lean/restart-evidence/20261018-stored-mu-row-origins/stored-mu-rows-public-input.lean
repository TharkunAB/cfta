import MicroCFTA.SourceCurrentStoredMuRowOrigins

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

#check @MicroCFTA.SourceCurrentStoredMuRowOrigins.Rows
#print MicroCFTA.SourceCurrentStoredMuRowOrigins.Rows
#print axioms MicroCFTA.SourceCurrentStoredMuRowOrigins.Rows

#check @MicroCFTA.SourceCurrentStoredMuRowOrigins.mu
#print MicroCFTA.SourceCurrentStoredMuRowOrigins.mu
#print axioms MicroCFTA.SourceCurrentStoredMuRowOrigins.mu

#check @MicroCFTA.SourceCurrentStoredMuRowOrigins.mu_complete
#print MicroCFTA.SourceCurrentStoredMuRowOrigins.mu_complete
#print axioms MicroCFTA.SourceCurrentStoredMuRowOrigins.mu_complete

