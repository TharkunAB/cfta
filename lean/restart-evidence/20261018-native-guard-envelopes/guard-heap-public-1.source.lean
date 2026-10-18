import MicroCFTA.SourceCurrentGuardHeapBounds
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
#check @MicroCFTA.SourceCurrentGuardHeapBounds.limits
#print MicroCFTA.SourceCurrentGuardHeapBounds.limits
#print axioms MicroCFTA.SourceCurrentGuardHeapBounds.limits
#check @MicroCFTA.SourceCurrentGuardHeapBounds.alphabet
#print MicroCFTA.SourceCurrentGuardHeapBounds.alphabet
#print axioms MicroCFTA.SourceCurrentGuardHeapBounds.alphabet
#check @MicroCFTA.SourceCurrentGuardHeapBounds.initial
#print MicroCFTA.SourceCurrentGuardHeapBounds.initial
#print axioms MicroCFTA.SourceCurrentGuardHeapBounds.initial
#check @MicroCFTA.SourceCurrentGuardHeapBounds.resident_complete
#print MicroCFTA.SourceCurrentGuardHeapBounds.resident_complete
#print axioms MicroCFTA.SourceCurrentGuardHeapBounds.resident_complete
