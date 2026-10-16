import MicroCFTA.SourceCurrentHereditaryNativeTransition

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

#print axioms MicroCFTA.SourceCurrentHereditaryNativeTransition.node_yielded
#check @MicroCFTA.SourceCurrentHereditaryNativeTransition.node_yielded

#print axioms MicroCFTA.SourceCurrentHereditaryNativeTransition.edge_yielded
#check @MicroCFTA.SourceCurrentHereditaryNativeTransition.edge_yielded
