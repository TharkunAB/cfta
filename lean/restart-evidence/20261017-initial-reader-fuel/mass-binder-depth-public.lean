import MicroCFTA.InternedValueMassBinderDepth

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.InternedValueMassBinderDepth.value_lt
#print axioms MicroCFTA.InternedValueMassBinderDepth.value_lt
#check @MicroCFTA.InternedValueMassBinderDepth.many_le
#print axioms MicroCFTA.InternedValueMassBinderDepth.many_le
#check @MicroCFTA.InternedValueMassBinderDepth.edges_le
#print axioms MicroCFTA.InternedValueMassBinderDepth.edges_le
#check @MicroCFTA.InternedValueMassBinderDepth.stored_bounded
#print axioms MicroCFTA.InternedValueMassBinderDepth.stored_bounded
