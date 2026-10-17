import MicroCFTA.SourceCurrentNativeEdgeHistory
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

#check @MicroCFTA.SourceCurrentNativeEdgeHistory.Writer
#print MicroCFTA.SourceCurrentNativeEdgeHistory.Writer
#print axioms MicroCFTA.SourceCurrentNativeEdgeHistory.Writer

#check @MicroCFTA.SourceCurrentNativeEdgeHistory.completed
#print MicroCFTA.SourceCurrentNativeEdgeHistory.completed
#print axioms MicroCFTA.SourceCurrentNativeEdgeHistory.completed

#check @MicroCFTA.SourceCurrentNativeEdgeHistory.Writer.live
#print MicroCFTA.SourceCurrentNativeEdgeHistory.Writer.live
#print axioms MicroCFTA.SourceCurrentNativeEdgeHistory.Writer.live

#check @MicroCFTA.SourceCurrentNativeEdgeHistory.warm
#print MicroCFTA.SourceCurrentNativeEdgeHistory.warm
#print axioms MicroCFTA.SourceCurrentNativeEdgeHistory.warm

#check @MicroCFTA.SourceCurrentNativeEdgeHistory.query
#print MicroCFTA.SourceCurrentNativeEdgeHistory.query
#print axioms MicroCFTA.SourceCurrentNativeEdgeHistory.query

#check @MicroCFTA.SourceCurrentNativeEdgeHistory.query_warm
#print MicroCFTA.SourceCurrentNativeEdgeHistory.query_warm
#print axioms MicroCFTA.SourceCurrentNativeEdgeHistory.query_warm
