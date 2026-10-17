import MicroCFTA.SourceCurrentNativeNodeWriterHistory
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentNativeNodeWriterHistory.Written
#print MicroCFTA.SourceCurrentNativeNodeWriterHistory.Written
#print axioms MicroCFTA.SourceCurrentNativeNodeWriterHistory.Written

#check @MicroCFTA.SourceCurrentNativeNodeWriterHistory.Written.grows
#print MicroCFTA.SourceCurrentNativeNodeWriterHistory.Written.grows
#print axioms MicroCFTA.SourceCurrentNativeNodeWriterHistory.Written.grows

#check @MicroCFTA.SourceCurrentNativeNodeWriterHistory.writers
#print MicroCFTA.SourceCurrentNativeNodeWriterHistory.writers
#print axioms MicroCFTA.SourceCurrentNativeNodeWriterHistory.writers

#check @MicroCFTA.SourceCurrentNativeNodeWriterHistory.warm
#print MicroCFTA.SourceCurrentNativeNodeWriterHistory.warm
#print axioms MicroCFTA.SourceCurrentNativeNodeWriterHistory.warm
