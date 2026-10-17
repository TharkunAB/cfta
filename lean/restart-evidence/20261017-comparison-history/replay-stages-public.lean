import MicroCFTA.SourceMergedComparisonReplayStages
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

#print axioms MicroCFTA.SourceMergedComparisonReplayStages.CallbackReplay
#check @MicroCFTA.SourceMergedComparisonReplayStages.CallbackReplay

#print axioms MicroCFTA.SourceMergedComparisonReplayStages.children_replay
#check @MicroCFTA.SourceMergedComparisonReplayStages.children_replay

#print axioms MicroCFTA.SourceMergedComparisonReplayStages.anyCover_replay
#check @MicroCFTA.SourceMergedComparisonReplayStages.anyCover_replay

#print axioms MicroCFTA.SourceMergedComparisonReplayStages.allRows_replay
#check @MicroCFTA.SourceMergedComparisonReplayStages.allRows_replay

