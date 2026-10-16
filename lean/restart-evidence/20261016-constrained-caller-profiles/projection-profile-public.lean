import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjectionProfile
#print axioms projectRows
#check @projectRows
#print axioms forestRows
#check @forestRows
#print axioms projectRows_base
#check @projectRows_base
#print axioms projectRows_step
#check @projectRows_step
#print axioms projectRows_mono
#check @projectRows_mono
#print axioms read_exact
#check @read_exact
#print axioms readAll_exact
#check @readAll_exact
#print axioms union
#check @union
#print axioms project
#check @project
#print axioms rows
#check @rows
#print axioms project_bounded
#check @project_bounded
#print axioms forest
#check @forest
#print axioms project_uniform
#check @project_uniform
#print axioms forest_uniform
#check @forest_uniform
