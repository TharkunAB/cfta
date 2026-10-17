import MicroCFTA.SourceCurrentGateGuard
import MicroCFTA.SourceCurrentGateFrameResources
import MicroCFTA.SourceCurrentSeededCallerNumeric

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentGateGuard.primary
#print axioms MicroCFTA.SourceCurrentGateGuard.primary
#print MicroCFTA.SourceCurrentGateGuard.primary

#check @MicroCFTA.SourceCurrentGateGuard.secondary
#print axioms MicroCFTA.SourceCurrentGateGuard.secondary
#print MicroCFTA.SourceCurrentGateGuard.secondary

#check @MicroCFTA.SourceCurrentGateFrameResources.forecast
#print axioms MicroCFTA.SourceCurrentGateFrameResources.forecast
#print MicroCFTA.SourceCurrentGateFrameResources.forecast

#check @MicroCFTA.SourceCurrentGateFrameResources.forecast_ge
#print axioms MicroCFTA.SourceCurrentGateFrameResources.forecast_ge
#print MicroCFTA.SourceCurrentGateFrameResources.forecast_ge

#check @MicroCFTA.SourceCurrentGateFrameResources.forecast_mono
#print axioms MicroCFTA.SourceCurrentGateFrameResources.forecast_mono
#print MicroCFTA.SourceCurrentGateFrameResources.forecast_mono

#check @MicroCFTA.SourceCurrentGateFrameResources.workerFuel
#print axioms MicroCFTA.SourceCurrentGateFrameResources.workerFuel
#print MicroCFTA.SourceCurrentGateFrameResources.workerFuel

#check @MicroCFTA.SourceCurrentGateFrameResources.workerFuel_mono
#print axioms MicroCFTA.SourceCurrentGateFrameResources.workerFuel_mono
#print MicroCFTA.SourceCurrentGateFrameResources.workerFuel_mono

#check @MicroCFTA.SourceCurrentGateFrameResources.primary
#print axioms MicroCFTA.SourceCurrentGateFrameResources.primary
#print MicroCFTA.SourceCurrentGateFrameResources.primary

#check @MicroCFTA.SourceCurrentGateFrameResources.secondary
#print axioms MicroCFTA.SourceCurrentGateFrameResources.secondary
#print MicroCFTA.SourceCurrentGateFrameResources.secondary

#check @MicroCFTA.SourceCurrentSeededCallerNumeric.of_receipt
#print axioms MicroCFTA.SourceCurrentSeededCallerNumeric.of_receipt
#print MicroCFTA.SourceCurrentSeededCallerNumeric.of_receipt

#check @MicroCFTA.SourceCurrentSeededCallerNumeric.complete
#print axioms MicroCFTA.SourceCurrentSeededCallerNumeric.complete
#print MicroCFTA.SourceCurrentSeededCallerNumeric.complete

