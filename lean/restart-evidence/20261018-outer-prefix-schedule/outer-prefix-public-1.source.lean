import MicroCFTA.SourceCurrentOuterInitialPrefix

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

#check @MicroCFTA.SourceCurrentOuterInitialPrefix.forecast
#print MicroCFTA.SourceCurrentOuterInitialPrefix.forecast
#print axioms MicroCFTA.SourceCurrentOuterInitialPrefix.forecast

#check @MicroCFTA.SourceCurrentOuterInitialPrefix.forecast_ge
#print MicroCFTA.SourceCurrentOuterInitialPrefix.forecast_ge
#print axioms MicroCFTA.SourceCurrentOuterInitialPrefix.forecast_ge

#check @MicroCFTA.SourceCurrentOuterInitialPrefix.StepSeed
#print MicroCFTA.SourceCurrentOuterInitialPrefix.StepSeed
#print axioms MicroCFTA.SourceCurrentOuterInitialPrefix.StepSeed

#check @MicroCFTA.SourceCurrentOuterInitialPrefix.SeedTrace
#print MicroCFTA.SourceCurrentOuterInitialPrefix.SeedTrace
#print axioms MicroCFTA.SourceCurrentOuterInitialPrefix.SeedTrace

#check @MicroCFTA.SourceCurrentOuterInitialPrefix.SeedTrace.refl
#print MicroCFTA.SourceCurrentOuterInitialPrefix.SeedTrace.refl
#print axioms MicroCFTA.SourceCurrentOuterInitialPrefix.SeedTrace.refl

#check @MicroCFTA.SourceCurrentOuterInitialPrefix.SeedTrace.snoc
#print MicroCFTA.SourceCurrentOuterInitialPrefix.SeedTrace.snoc
#print axioms MicroCFTA.SourceCurrentOuterInitialPrefix.SeedTrace.snoc

#check @MicroCFTA.SourceCurrentOuterInitialPrefix.reached
#print MicroCFTA.SourceCurrentOuterInitialPrefix.reached
#print axioms MicroCFTA.SourceCurrentOuterInitialPrefix.reached

