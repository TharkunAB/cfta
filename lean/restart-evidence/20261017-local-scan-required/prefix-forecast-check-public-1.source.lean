import MicroCFTA.SourceCurrentScanRequiredWorker
import MicroCFTA.SourceCurrentScanRequiredForecast
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

#check @MicroCFTA.SourceCurrentScanRequiredWorker.Result
#print axioms MicroCFTA.SourceCurrentScanRequiredWorker.Result

#check @MicroCFTA.SourceCurrentScanRequiredWorker.prepare
#print axioms MicroCFTA.SourceCurrentScanRequiredWorker.prepare

#check @MicroCFTA.SourceCurrentScanRequiredWorker.classes
#print axioms MicroCFTA.SourceCurrentScanRequiredWorker.classes

#check @MicroCFTA.SourceCurrentScanRequiredForecast.scanProfile
#print axioms MicroCFTA.SourceCurrentScanRequiredForecast.scanProfile

#check @MicroCFTA.SourceCurrentScanRequiredForecast.finalProfile
#print axioms MicroCFTA.SourceCurrentScanRequiredForecast.finalProfile

#check @MicroCFTA.SourceCurrentScanRequiredForecast.scan_le
#print axioms MicroCFTA.SourceCurrentScanRequiredForecast.scan_le

#check @MicroCFTA.SourceCurrentScanRequiredForecast.fuel
#print axioms MicroCFTA.SourceCurrentScanRequiredForecast.fuel

#check @MicroCFTA.SourceCurrentScanRequiredForecast.scan_fuel
#print axioms MicroCFTA.SourceCurrentScanRequiredForecast.scan_fuel

#check @MicroCFTA.SourceCurrentScanRequiredForecast.required_worker
#print axioms MicroCFTA.SourceCurrentScanRequiredForecast.required_worker

#check @MicroCFTA.SourceCurrentScanRequiredForecast.required_reader
#print axioms MicroCFTA.SourceCurrentScanRequiredForecast.required_reader
