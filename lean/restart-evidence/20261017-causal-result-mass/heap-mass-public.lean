import MicroCFTA.InternedValueMassConstructors

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

#print axioms MicroCFTA.InternedValueMassHeap.Stored
#check @MicroCFTA.InternedValueMassHeap.Stored
#print axioms MicroCFTA.InternedValueMassHeap.Stored.mk
#check @MicroCFTA.InternedValueMassHeap.Stored.mk
#print axioms MicroCFTA.InternedValueMassHeap.Stored.positive
#check @MicroCFTA.InternedValueMassHeap.Stored.positive
#print axioms MicroCFTA.InternedValueMassHeap.Stored.nodes
#check @MicroCFTA.InternedValueMassHeap.Stored.nodes
#print axioms MicroCFTA.InternedValueMassHeap.Stored.edges
#check @MicroCFTA.InternedValueMassHeap.Stored.edges
#print axioms MicroCFTA.InternedValueMassHeap.Stored.mono
#check @MicroCFTA.InternedValueMassHeap.Stored.mono
#print axioms MicroCFTA.InternedValueMassHeap.empty_stored
#check @MicroCFTA.InternedValueMassHeap.empty_stored
#print axioms MicroCFTA.InternedValueMassHeap.initialBound
#check @MicroCFTA.InternedValueMassHeap.initialBound
#print axioms MicroCFTA.InternedValueMassHeap.initial
#check @MicroCFTA.InternedValueMassHeap.initial
#print axioms MicroCFTA.InternedValueMassHeap.available
#check @MicroCFTA.InternedValueMassHeap.available
#print axioms MicroCFTA.InternedValueMassHeap.resident
#check @MicroCFTA.InternedValueMassHeap.resident
#print axioms MicroCFTA.InternedValueMassHeap.Stored.node_cache
#check @MicroCFTA.InternedValueMassHeap.Stored.node_cache
#print axioms MicroCFTA.InternedValueMassHeap.Stored.edge_cache
#check @MicroCFTA.InternedValueMassHeap.Stored.edge_cache
#print axioms MicroCFTA.InternedValueMassHeap.Stored.put_node
#check @MicroCFTA.InternedValueMassHeap.Stored.put_node
#print axioms MicroCFTA.InternedValueMassHeap.Stored.put_edge
#check @MicroCFTA.InternedValueMassHeap.Stored.put_edge
#print axioms MicroCFTA.InternedValueMassHeap.node_step
#check @MicroCFTA.InternedValueMassHeap.node_step
#print axioms MicroCFTA.InternedValueMassHeap.edge_step
#check @MicroCFTA.InternedValueMassHeap.edge_step
#print axioms MicroCFTA.InternedValueMassConstructors.canonical_edges_le
#check @MicroCFTA.InternedValueMassConstructors.canonical_edges_le
#print axioms MicroCFTA.InternedValueMassConstructors.normalized_edges_le
#check @MicroCFTA.InternedValueMassConstructors.normalized_edges_le
#print axioms MicroCFTA.InternedValueMassConstructors.flattened_values_le
#check @MicroCFTA.InternedValueMassConstructors.flattened_values_le
#print axioms MicroCFTA.InternedValueMassConstructors.distinct_values_le
#check @MicroCFTA.InternedValueMassConstructors.distinct_values_le
#print axioms MicroCFTA.InternedValueMassConstructors.ordinary_edges_le
#check @MicroCFTA.InternedValueMassConstructors.ordinary_edges_le
#print axioms MicroCFTA.InternedValueMassConstructors.edge
#check @MicroCFTA.InternedValueMassConstructors.edge
#print axioms MicroCFTA.InternedValueMassConstructors.node
#check @MicroCFTA.InternedValueMassConstructors.node
#print axioms MicroCFTA.InternedValueMassConstructors.union
#check @MicroCFTA.InternedValueMassConstructors.union
#print axioms MicroCFTA.InternedValueMassConstructors.cleanup_le
#check @MicroCFTA.InternedValueMassConstructors.cleanup_le
#print axioms MicroCFTA.InternedValueMassConstructors.filter
#check @MicroCFTA.InternedValueMassConstructors.filter
