import MicroCFTA.SourceCurrentAllocatedRowReadNumeric

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

#print axioms MicroCFTA.InternedValueMassBinderDepth.value_lt
#check @MicroCFTA.InternedValueMassBinderDepth.value_lt

#print axioms MicroCFTA.InternedValueMassBinderDepth.many_le
#check @MicroCFTA.InternedValueMassBinderDepth.many_le

#print axioms MicroCFTA.InternedValueMassBinderDepth.edges_le
#check @MicroCFTA.InternedValueMassBinderDepth.edges_le

#print axioms MicroCFTA.InternedValueMassBinderDepth.stored_bounded
#check @MicroCFTA.InternedValueMassBinderDepth.stored_bounded

#print axioms MicroCFTA.SourceCurrentAllocatedReaderNumeric.initialControl
#check @MicroCFTA.SourceCurrentAllocatedReaderNumeric.initialControl

#print axioms MicroCFTA.SourceCurrentAllocatedReaderNumeric.collectFuel
#check @MicroCFTA.SourceCurrentAllocatedReaderNumeric.collectFuel

#print axioms MicroCFTA.SourceCurrentAllocatedReaderNumeric.fuel
#check @MicroCFTA.SourceCurrentAllocatedReaderNumeric.fuel

#print axioms MicroCFTA.SourceCurrentAllocatedReaderNumeric.path_control
#check @MicroCFTA.SourceCurrentAllocatedReaderNumeric.path_control

#print axioms MicroCFTA.SourceCurrentAllocatedReaderNumeric.control_complete
#check @MicroCFTA.SourceCurrentAllocatedReaderNumeric.control_complete

#print axioms MicroCFTA.SourceCurrentAllocatedReaderNumeric.collect_complete
#check @MicroCFTA.SourceCurrentAllocatedReaderNumeric.collect_complete

#print axioms MicroCFTA.SourceCurrentAllocatedRowReadNumeric.readFuel
#check @MicroCFTA.SourceCurrentAllocatedRowReadNumeric.readFuel

#print axioms MicroCFTA.SourceCurrentAllocatedRowReadNumeric.complete_bound
#check @MicroCFTA.SourceCurrentAllocatedRowReadNumeric.complete_bound

#print axioms MicroCFTA.SourceCurrentAllocatedRowReadNumeric.complete
#check @MicroCFTA.SourceCurrentAllocatedRowReadNumeric.complete
