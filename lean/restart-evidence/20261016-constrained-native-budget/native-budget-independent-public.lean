import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudget
#print axioms nodeBudget
#check @nodeBudget
#print axioms edgeBudget
#check @edgeBudget
#print axioms node_prefix_budget
#check @node_prefix_budget
#print axioms node_prefix_capacity
#check @node_prefix_capacity
#print axioms edge_prefix_budget
#check @edge_prefix_budget
#print axioms edge_prefix_capacity
#check @edge_prefix_capacity
