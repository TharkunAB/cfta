import MicroCFTA.SourceCurrentConstrainedCapRequired

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

#print axioms MicroCFTA.SourceCurrentConstrainedCapExposure.collect
#check @MicroCFTA.SourceCurrentConstrainedCapExposure.collect
#print axioms MicroCFTA.SourceCurrentConstrainedCapExposure.nodeEdges
#check @MicroCFTA.SourceCurrentConstrainedCapExposure.nodeEdges
#print axioms MicroCFTA.SourceCurrentConstrainedCapExposure.head
#check @MicroCFTA.SourceCurrentConstrainedCapExposure.head
#print axioms MicroCFTA.SourceCurrentConstrainedCapRequired.node
#check @MicroCFTA.SourceCurrentConstrainedCapRequired.node
#print axioms MicroCFTA.SourceCurrentConstrainedCapRequired.children
#check @MicroCFTA.SourceCurrentConstrainedCapRequired.children
#print axioms MicroCFTA.SourceCurrentConstrainedCapRequired.rows
#check @MicroCFTA.SourceCurrentConstrainedCapRequired.rows
#print axioms MicroCFTA.SourceCurrentConstrainedCapRequired.requireAll
#check @MicroCFTA.SourceCurrentConstrainedCapRequired.requireAll
