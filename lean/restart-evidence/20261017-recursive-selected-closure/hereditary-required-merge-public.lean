import MicroCFTA.SourceCurrentHereditaryConstructors
import MicroCFTA.SourceCurrentHereditaryMerge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.SourceCurrentHereditaryConstructors.Edge
#check @MicroCFTA.SourceCurrentHereditaryConstructors.Edge

#print axioms MicroCFTA.SourceCurrentHereditaryConstructors.node_edge
#check @MicroCFTA.SourceCurrentHereditaryConstructors.node_edge

#print axioms MicroCFTA.SourceCurrentHereditaryConstructors.makeEdge
#check @MicroCFTA.SourceCurrentHereditaryConstructors.makeEdge

#print axioms MicroCFTA.SourceCurrentHereditaryConstructors.makeNode
#check @MicroCFTA.SourceCurrentHereditaryConstructors.makeNode

#print axioms MicroCFTA.SourceCurrentHereditaryConstructors.ordinaryUnion
#check @MicroCFTA.SourceCurrentHereditaryConstructors.ordinaryUnion

#print axioms MicroCFTA.SourceCurrentHereditaryConstructors.union_member
#check @MicroCFTA.SourceCurrentHereditaryConstructors.union_member

#print axioms MicroCFTA.SourceCurrentHereditaryConstructors.makeUnion
#check @MicroCFTA.SourceCurrentHereditaryConstructors.makeUnion

#print axioms MicroCFTA.SourceCurrentHereditaryMerge.Certificate
#check @MicroCFTA.SourceCurrentHereditaryMerge.Certificate

#print axioms MicroCFTA.SourceCurrentHereditaryMerge.Stored
#check @MicroCFTA.SourceCurrentHereditaryMerge.Stored

#print axioms MicroCFTA.SourceCurrentHereditaryMerge.stored_empty
#check @MicroCFTA.SourceCurrentHereditaryMerge.stored_empty

#print axioms MicroCFTA.SourceCurrentHereditaryMerge.stored_remember
#check @MicroCFTA.SourceCurrentHereditaryMerge.stored_remember

#print axioms MicroCFTA.SourceCurrentHereditaryMerge.Contract
#check @MicroCFTA.SourceCurrentHereditaryMerge.Contract

#print axioms MicroCFTA.SourceCurrentHereditaryMerge.Certified
#check @MicroCFTA.SourceCurrentHereditaryMerge.Certified

#print axioms MicroCFTA.SourceCurrentHereditaryMerge.run
#check @MicroCFTA.SourceCurrentHereditaryMerge.run

#print axioms MicroCFTA.SourceCurrentHereditaryMerge.call
#check @MicroCFTA.SourceCurrentHereditaryMerge.call

#print axioms MicroCFTA.SourceCurrentHereditaryMerge.cold
#check @MicroCFTA.SourceCurrentHereditaryMerge.cold
