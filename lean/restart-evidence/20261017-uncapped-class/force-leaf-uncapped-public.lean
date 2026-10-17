import MicroCFTA.SourceCurrentForceNumeric
import MicroCFTA.SourceCurrentLeafNumeric
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentForceNumeric.complete
#print axioms MicroCFTA.SourceCurrentForceNumeric.complete
#print MicroCFTA.SourceCurrentForceNumeric.complete

#check @MicroCFTA.SourceCurrentLeafNumeric.complete
#print axioms MicroCFTA.SourceCurrentLeafNumeric.complete
#print MicroCFTA.SourceCurrentLeafNumeric.complete

