import MicroCFTA.SourceCurrentNativeGuardCode
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
#check @MicroCFTA.SourceCurrentNativeGuardCode.Fields
#print axioms MicroCFTA.SourceCurrentNativeGuardCode.Fields
#check @MicroCFTA.SourceCurrentNativeGuardCode.work_mono
#print axioms MicroCFTA.SourceCurrentNativeGuardCode.work_mono
#check @MicroCFTA.SourceCurrentNativeGuardCode.mono
#print axioms MicroCFTA.SourceCurrentNativeGuardCode.mono
#check @MicroCFTA.SourceCurrentNativeGuardCode.bind
#print axioms MicroCFTA.SourceCurrentNativeGuardCode.bind
#check @MicroCFTA.SourceCurrentNativeGuardCode.walk
#print axioms MicroCFTA.SourceCurrentNativeGuardCode.walk
#check @MicroCFTA.SourceCurrentNativeGuardCode.compileNode_fields
#print axioms MicroCFTA.SourceCurrentNativeGuardCode.compileNode_fields
#check @MicroCFTA.SourceCurrentNativeGuardCode.sentinel_fields
#print axioms MicroCFTA.SourceCurrentNativeGuardCode.sentinel_fields
#check @MicroCFTA.SourceCurrentNativeGuardCode.children_fields
#print axioms MicroCFTA.SourceCurrentNativeGuardCode.children_fields
#check @MicroCFTA.SourceCurrentNativeGuardCode.body_fields
#print axioms MicroCFTA.SourceCurrentNativeGuardCode.body_fields
