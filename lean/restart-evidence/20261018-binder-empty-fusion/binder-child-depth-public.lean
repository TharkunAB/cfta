import MicroCFTA.SourceCurrentSourceChildDepth

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

#check @MicroCFTA.SourceCurrentSourceChildDepth.node
#print MicroCFTA.SourceCurrentSourceChildDepth.node
#print axioms MicroCFTA.SourceCurrentSourceChildDepth.node
#check @MicroCFTA.SourceCurrentSourceChildDepth.union
#print MicroCFTA.SourceCurrentSourceChildDepth.union
#print axioms MicroCFTA.SourceCurrentSourceChildDepth.union
