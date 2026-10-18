import MicroCFTA.SourceCurrentFiniteRootReconstruction
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

#check @MicroCFTA.SourceCurrentFiniteRootReconstruction.Executions
#print MicroCFTA.SourceCurrentFiniteRootReconstruction.Executions
#print axioms MicroCFTA.SourceCurrentFiniteRootReconstruction.Executions
#check @MicroCFTA.SourceCurrentFiniteRootReconstruction.reconstruct
#print MicroCFTA.SourceCurrentFiniteRootReconstruction.reconstruct
#print axioms MicroCFTA.SourceCurrentFiniteRootReconstruction.reconstruct
