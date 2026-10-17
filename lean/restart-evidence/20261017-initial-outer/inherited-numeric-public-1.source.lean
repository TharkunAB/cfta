import MicroCFTA.SourceCurrentInheritedNumeric
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

#print axioms MicroCFTA.SourceCurrentInheritedNumeric.complete
#check @MicroCFTA.SourceCurrentInheritedNumeric.complete
#print MicroCFTA.SourceCurrentInheritedNumeric.complete
#print axioms MicroCFTA.SourceCurrentInheritedNumeric.resident_complete
#check @MicroCFTA.SourceCurrentInheritedNumeric.resident_complete
#print MicroCFTA.SourceCurrentInheritedNumeric.resident_complete
#print axioms MicroCFTA.SourceCurrentInheritedNumeric.descent
#check @MicroCFTA.SourceCurrentInheritedNumeric.descent
#print MicroCFTA.SourceCurrentInheritedNumeric.descent
#print axioms MicroCFTA.SourceCurrentInheritedNumeric.prefix_descent
#check @MicroCFTA.SourceCurrentInheritedNumeric.prefix_descent
#print MicroCFTA.SourceCurrentInheritedNumeric.prefix_descent
