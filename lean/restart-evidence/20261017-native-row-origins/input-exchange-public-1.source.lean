import MicroCFTA.SourceCurrentNativeInputExchange

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentNativeInputExchange.live_agreement
#print MicroCFTA.SourceCurrentNativeInputExchange.live_agreement
#print axioms MicroCFTA.SourceCurrentNativeInputExchange.live_agreement

#check @MicroCFTA.SourceCurrentNativeInputExchange.of_completed
#print MicroCFTA.SourceCurrentNativeInputExchange.of_completed
#print axioms MicroCFTA.SourceCurrentNativeInputExchange.of_completed

#check @MicroCFTA.SourceCurrentNativeInputExchange.complete
#print MicroCFTA.SourceCurrentNativeInputExchange.complete
#print axioms MicroCFTA.SourceCurrentNativeInputExchange.complete

#check @MicroCFTA.SourceCurrentNativeInputExchange.local_complete
#print MicroCFTA.SourceCurrentNativeInputExchange.local_complete
#print axioms MicroCFTA.SourceCurrentNativeInputExchange.local_complete

