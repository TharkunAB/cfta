import MicroCFTA.SourceCurrentNativeMuHistory
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

#check @MicroCFTA.SourceCurrentNativeMuHistory.callback
#print MicroCFTA.SourceCurrentNativeMuHistory.callback
#print axioms MicroCFTA.SourceCurrentNativeMuHistory.callback

#check @MicroCFTA.SourceCurrentNativeMuHistory.construct
#print MicroCFTA.SourceCurrentNativeMuHistory.construct
#print axioms MicroCFTA.SourceCurrentNativeMuHistory.construct

#check @MicroCFTA.SourceCurrentNativeMuHistory.maybeMu
#print MicroCFTA.SourceCurrentNativeMuHistory.maybeMu
#print axioms MicroCFTA.SourceCurrentNativeMuHistory.maybeMu

