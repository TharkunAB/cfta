import MicroCFTA.SourceCurrentStoredNodeExpansion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentStoredNodeExpansion.RowCalls
#print MicroCFTA.SourceCurrentStoredNodeExpansion.RowCalls
#print axioms MicroCFTA.SourceCurrentStoredNodeExpansion.RowCalls

#check @MicroCFTA.SourceCurrentStoredNodeExpansion.Expansion
#print MicroCFTA.SourceCurrentStoredNodeExpansion.Expansion
#print axioms MicroCFTA.SourceCurrentStoredNodeExpansion.Expansion

#check @MicroCFTA.SourceCurrentStoredNodeExpansion.node_warm
#print MicroCFTA.SourceCurrentStoredNodeExpansion.node_warm
#print axioms MicroCFTA.SourceCurrentStoredNodeExpansion.node_warm

