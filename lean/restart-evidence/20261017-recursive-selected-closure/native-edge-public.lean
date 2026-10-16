import MicroCFTA.SourceCurrentHereditaryNativeEdge

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

#print axioms MicroCFTA.SourceCurrentHereditaryNativeEdge.children_certified
#check @MicroCFTA.SourceCurrentHereditaryNativeEdge.children_certified
#print axioms MicroCFTA.SourceCurrentHereditaryNativeEdge.sentinel_certified
#check @MicroCFTA.SourceCurrentHereditaryNativeEdge.sentinel_certified
#print axioms MicroCFTA.SourceCurrentHereditaryNativeEdge.body_certified
#check @MicroCFTA.SourceCurrentHereditaryNativeEdge.body_certified
