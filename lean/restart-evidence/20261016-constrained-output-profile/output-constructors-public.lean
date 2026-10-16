import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
#print axioms children_of_members
#check @children_of_members
#print axioms rows_of_members
#check @rows_of_members
#print axioms rows_subset
#check @rows_subset
#print axioms rows_filter
#check @rows_filter
#print axioms rows_canonical
#check @rows_canonical
#print axioms canonical_length_le
#check @canonical_length_le
#print axioms normalized_rows
#check @normalized_rows
#print axioms children_of_all₂
#check @children_of_all₂
#print axioms rows_of_all₂
#check @rows_of_all₂
#print axioms makeEdge
#check @makeEdge
#print axioms makeNode
#check @makeNode
