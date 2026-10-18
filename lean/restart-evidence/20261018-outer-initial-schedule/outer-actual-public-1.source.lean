import MicroCFTA.SourceCurrentOuterInitialActual

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

#check @MicroCFTA.SourceCurrentOuterInitialActual.node_call
#print MicroCFTA.SourceCurrentOuterInitialActual.node_call
#print axioms MicroCFTA.SourceCurrentOuterInitialActual.node_call

#check @MicroCFTA.SourceCurrentOuterInitialActual.node_body
#print MicroCFTA.SourceCurrentOuterInitialActual.node_body
#print axioms MicroCFTA.SourceCurrentOuterInitialActual.node_body

#check @MicroCFTA.SourceCurrentOuterInitialActual.rows
#print MicroCFTA.SourceCurrentOuterInitialActual.rows
#print axioms MicroCFTA.SourceCurrentOuterInitialActual.rows

#check @MicroCFTA.SourceCurrentOuterInitialActual.descendants
#print MicroCFTA.SourceCurrentOuterInitialActual.descendants
#print axioms MicroCFTA.SourceCurrentOuterInitialActual.descendants

#check @MicroCFTA.SourceCurrentOuterInitialActual.children
#print MicroCFTA.SourceCurrentOuterInitialActual.children
#print axioms MicroCFTA.SourceCurrentOuterInitialActual.children

#check @MicroCFTA.SourceCurrentOuterInitialActual.walk
#print MicroCFTA.SourceCurrentOuterInitialActual.walk
#print axioms MicroCFTA.SourceCurrentOuterInitialActual.walk

