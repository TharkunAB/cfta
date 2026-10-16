import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeProfile

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeProfile

#print axioms NodeShape
#check @NodeShape
#print axioms RowsShape
#check @RowsShape
#print axioms EdgeShape
#check @EdgeShape
#print axioms ChildrenShape
#check @ChildrenShape
#print axioms limits
#check @limits
#print axioms rowsLimits
#check @rowsLimits
#print axioms edgeLimits
#check @edgeLimits
#print axioms childrenLimits
#check @childrenLimits
#print axioms NodeShape.mono
#check @NodeShape.mono
#print axioms RowsShape.mono
#check @RowsShape.mono
#print axioms EdgeShape.mono
#check @EdgeShape.mono
#print axioms ChildrenShape.mono
#check @ChildrenShape.mono
#print axioms RowsShape.member
#check @RowsShape.member
#print axioms ChildrenShape.member
#check @ChildrenShape.member
#print axioms NodeShape.rows
#check @NodeShape.rows
#print axioms NodeShape.nodeEdges
#check @NodeShape.nodeEdges
#print axioms NodeShape.length
#check @NodeShape.length
#print axioms EdgeShape.arity
#check @EdgeShape.arity
#print axioms EdgeShape.children
#check @EdgeShape.children
#print axioms NodeShape.child
#check @NodeShape.child
#print axioms NodeShape.domain
#check @NodeShape.domain
#print axioms RowsShape.domain
#check @RowsShape.domain
#print axioms EdgeShape.domain
#check @EdgeShape.domain
#print axioms ChildrenShape.domain
#check @ChildrenShape.domain
#print axioms node_shape_self
#check @node_shape_self
#print axioms rows_shape_self
#check @rows_shape_self
#print axioms edge_shape_self
#check @edge_shape_self
#print axioms children_shape_self
#check @children_shape_self
#print axioms node_shape_of_root
#check @node_shape_of_root
#print axioms pairs_length_le
#check @pairs_length_le
#print axioms pairs_length_bound
#check @pairs_length_bound
