import MicroCFTA.SourceCurrentFiniteReconstruction
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentFiniteReconstruction.complete
#print MicroCFTA.SourceCurrentFiniteReconstruction.complete
#print axioms MicroCFTA.SourceCurrentFiniteReconstruction.complete
#check @MicroCFTA.SourceCurrentFiniteReconstruction.binder_free
#print MicroCFTA.SourceCurrentFiniteReconstruction.binder_free
#print axioms MicroCFTA.SourceCurrentFiniteReconstruction.binder_free
#check @MicroCFTA.SourceCurrentFiniteReconstruction.initial
#print MicroCFTA.SourceCurrentFiniteReconstruction.initial
#print axioms MicroCFTA.SourceCurrentFiniteReconstruction.initial
