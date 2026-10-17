import MicroCFTA.SourceCurrentOuterEdgeIdle

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentOuterEdgeIdle.EdgeIdle
#print MicroCFTA.SourceCurrentOuterEdgeIdle.EdgeIdle
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.EdgeIdle
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.NoEdgeBusy
#print MicroCFTA.SourceCurrentOuterEdgeIdle.NoEdgeBusy
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.NoEdgeBusy
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.Safe
#print MicroCFTA.SourceCurrentOuterEdgeIdle.Safe
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.Safe
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.initial
#print MicroCFTA.SourceCurrentOuterEdgeIdle.initial
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.initial
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.node_call
#print MicroCFTA.SourceCurrentOuterEdgeIdle.node_call
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.node_call
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.node_body
#print MicroCFTA.SourceCurrentOuterEdgeIdle.node_body
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.node_body
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.edge_call
#print MicroCFTA.SourceCurrentOuterEdgeIdle.edge_call
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.edge_call
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.edge_body
#print MicroCFTA.SourceCurrentOuterEdgeIdle.edge_body
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.edge_body
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.row_pass
#print MicroCFTA.SourceCurrentOuterEdgeIdle.row_pass
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.row_pass
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.descendant_pass
#print MicroCFTA.SourceCurrentOuterEdgeIdle.descendant_pass
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.descendant_pass
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.child_pass
#print MicroCFTA.SourceCurrentOuterEdgeIdle.child_pass
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.child_pass
#check @MicroCFTA.SourceCurrentOuterEdgeIdle.indexed_walk
#print MicroCFTA.SourceCurrentOuterEdgeIdle.indexed_walk
#print axioms MicroCFTA.SourceCurrentOuterEdgeIdle.indexed_walk
