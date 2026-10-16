import MicroCFTA.SourceCurrentHereditaryNativeCold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.pure_result
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.pure_result

#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.certified_bind
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.certified_bind

#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.node_law
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.node_law

#print axioms MicroCFTA.SourceCurrentHereditaryNativeControl.edge_law
#check @MicroCFTA.SourceCurrentHereditaryNativeControl.edge_law

#print axioms MicroCFTA.SourceCurrentHereditaryNativeTrace.completed
#check @MicroCFTA.SourceCurrentHereditaryNativeTrace.completed

#print axioms MicroCFTA.SourceCurrentHereditaryNativeCold.cold_complete
#check @MicroCFTA.SourceCurrentHereditaryNativeCold.cold_complete

