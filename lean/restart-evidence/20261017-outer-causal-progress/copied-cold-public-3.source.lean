import MicroCFTA.SourceCurrentOuterCopiedCold
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
#check @MicroCFTA.SourceCurrentOuterCopiedCold.copied_cold_while_owners_active
set_option pp.raw true in
#print MicroCFTA.SourceCurrentOuterCopiedCold.copied_cold_while_owners_active
#print axioms MicroCFTA.SourceCurrentOuterCopiedCold.copied_cold_while_owners_active
