import MicroCFTA.SourceCurrentActualLocalRowOrigins
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

#check @MicroCFTA.SourceCurrentActualLocalRowOrigins.untouched_fold
#print MicroCFTA.SourceCurrentActualLocalRowOrigins.untouched_fold
#print axioms MicroCFTA.SourceCurrentActualLocalRowOrigins.untouched_fold

#check @MicroCFTA.SourceCurrentActualLocalRowOrigins.untouched_pass
#print MicroCFTA.SourceCurrentActualLocalRowOrigins.untouched_pass
#print axioms MicroCFTA.SourceCurrentActualLocalRowOrigins.untouched_pass

#check @MicroCFTA.SourceCurrentActualLocalRowOrigins.classes
#print MicroCFTA.SourceCurrentActualLocalRowOrigins.classes
#print axioms MicroCFTA.SourceCurrentActualLocalRowOrigins.classes
