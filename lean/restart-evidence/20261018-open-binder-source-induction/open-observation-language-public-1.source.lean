import MicroCFTA.SourceCurrentOpenObservationLanguage

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentOpenObservationLanguage.finite
#print MicroCFTA.SourceCurrentOpenObservationLanguage.finite
#print axioms MicroCFTA.SourceCurrentOpenObservationLanguage.finite
#check @MicroCFTA.SourceCurrentOpenObservationLanguage.all_depths
#print MicroCFTA.SourceCurrentOpenObservationLanguage.all_depths
#print axioms MicroCFTA.SourceCurrentOpenObservationLanguage.all_depths
#check @MicroCFTA.SourceCurrentOpenObservationLanguage.directed
#print MicroCFTA.SourceCurrentOpenObservationLanguage.directed
#print axioms MicroCFTA.SourceCurrentOpenObservationLanguage.directed
