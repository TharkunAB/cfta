import MicroCFTA.SourceCurrentNativeEdgeWriterRetention

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

#check @MicroCFTA.SourceCurrentNativeEdgeWriterRetention.Written
#print MicroCFTA.SourceCurrentNativeEdgeWriterRetention.Written
#print axioms MicroCFTA.SourceCurrentNativeEdgeWriterRetention.Written

#check @MicroCFTA.SourceCurrentNativeEdgeWriterRetention.Written.forget
#print MicroCFTA.SourceCurrentNativeEdgeWriterRetention.Written.forget
#print axioms MicroCFTA.SourceCurrentNativeEdgeWriterRetention.Written.forget

#check @MicroCFTA.SourceCurrentNativeEdgeWriterRetention.edge_writers
#print MicroCFTA.SourceCurrentNativeEdgeWriterRetention.edge_writers
#print axioms MicroCFTA.SourceCurrentNativeEdgeWriterRetention.edge_writers

