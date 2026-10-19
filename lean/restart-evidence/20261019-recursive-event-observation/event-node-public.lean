import MicroCFTA.SourceCurrentClassEventExecutions

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

#check @MicroCFTA.SourceCurrentClassEventExecutions.Source
#print MicroCFTA.SourceCurrentClassEventExecutions.Source
#print axioms MicroCFTA.SourceCurrentClassEventExecutions.Source

#check @MicroCFTA.SourceCurrentClassEventExecutions.Source.later
#print MicroCFTA.SourceCurrentClassEventExecutions.Source.later
#print axioms MicroCFTA.SourceCurrentClassEventExecutions.Source.later

#check @MicroCFTA.SourceCurrentClassEventExecutions.occurrence
#print MicroCFTA.SourceCurrentClassEventExecutions.occurrence
#print axioms MicroCFTA.SourceCurrentClassEventExecutions.occurrence

#check @MicroCFTA.SourceCurrentClassEventExecutions.node
#print MicroCFTA.SourceCurrentClassEventExecutions.node
#print axioms MicroCFTA.SourceCurrentClassEventExecutions.node

#check @MicroCFTA.SourceCurrentClassEventExecutions.children
#print MicroCFTA.SourceCurrentClassEventExecutions.children
#print axioms MicroCFTA.SourceCurrentClassEventExecutions.children

