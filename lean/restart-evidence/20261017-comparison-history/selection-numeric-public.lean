import MicroCFTA.SourceMergedSelectionNumeric

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.SourceMergedSelectionNumeric.any_recorded
#check @MicroCFTA.SourceMergedSelectionNumeric.any_recorded

#print axioms MicroCFTA.SourceMergedSelectionNumeric.retain_recorded
#check @MicroCFTA.SourceMergedSelectionNumeric.retain_recorded

#print axioms MicroCFTA.SourceMergedSelectionNumeric.select_recorded
#check @MicroCFTA.SourceMergedSelectionNumeric.select_recorded

#print axioms MicroCFTA.SourceMergedSelectionNumeric.any_replay
#check @MicroCFTA.SourceMergedSelectionNumeric.any_replay

#print axioms MicroCFTA.SourceMergedSelectionNumeric.retain_replay
#check @MicroCFTA.SourceMergedSelectionNumeric.retain_replay

#print axioms MicroCFTA.SourceMergedSelectionNumeric.select_replay
#check @MicroCFTA.SourceMergedSelectionNumeric.select_replay

#print axioms MicroCFTA.SourceMergedSelectionNumeric.select_complete
#check @MicroCFTA.SourceMergedSelectionNumeric.select_complete
