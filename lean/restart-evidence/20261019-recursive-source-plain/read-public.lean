import MicroCFTA.SourceCurrentRecursivePlainRead

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentRecursivePlainRead.project
#print MicroCFTA.SourceCurrentRecursivePlainRead.project
#print axioms MicroCFTA.SourceCurrentRecursivePlainRead.project

#check @MicroCFTA.SourceCurrentRecursivePlainRead.project_read
#print MicroCFTA.SourceCurrentRecursivePlainRead.project_read
#print axioms MicroCFTA.SourceCurrentRecursivePlainRead.project_read

