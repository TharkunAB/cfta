import MicroCFTA.SourceMergedComparisonHistory

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.SourceMergedComparisonHistory.Recorded
#check @MicroCFTA.SourceMergedComparisonHistory.Recorded

#print axioms MicroCFTA.SourceMergedComparisonHistory.Recorded.trans
#check @MicroCFTA.SourceMergedComparisonHistory.Recorded.trans

#print axioms MicroCFTA.SourceMergedComparisonHistory.pure_recorded
#check @MicroCFTA.SourceMergedComparisonHistory.pure_recorded

#print axioms MicroCFTA.SourceMergedComparisonHistory.read_recorded
#check @MicroCFTA.SourceMergedComparisonHistory.read_recorded

#print axioms MicroCFTA.SourceMergedComparisonHistory.Callback
#check @MicroCFTA.SourceMergedComparisonHistory.Callback

#print axioms MicroCFTA.SourceMergedComparisonHistory.children_recorded
#check @MicroCFTA.SourceMergedComparisonHistory.children_recorded

#print axioms MicroCFTA.SourceMergedComparisonHistory.anyCover_recorded
#check @MicroCFTA.SourceMergedComparisonHistory.anyCover_recorded

#print axioms MicroCFTA.SourceMergedComparisonHistory.allRows_recorded
#check @MicroCFTA.SourceMergedComparisonHistory.allRows_recorded

#print axioms MicroCFTA.SourceMergedComparisonHistory.check_recorded
#check @MicroCFTA.SourceMergedComparisonHistory.check_recorded
