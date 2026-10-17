import MicroCFTA.SourceMergedComparisonNumeric

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

#print axioms MicroCFTA.SourceMergedComparisonNumeric.readerFuel
#check @MicroCFTA.SourceMergedComparisonNumeric.readerFuel

#print axioms MicroCFTA.SourceMergedComparisonNumeric.comparisonFuel
#check @MicroCFTA.SourceMergedComparisonNumeric.comparisonFuel

#print axioms MicroCFTA.SourceMergedComparisonNumeric.read_replay
#check @MicroCFTA.SourceMergedComparisonNumeric.read_replay

#print axioms MicroCFTA.SourceMergedComparisonNumeric.check_replay
#check @MicroCFTA.SourceMergedComparisonNumeric.check_replay

#print axioms MicroCFTA.SourceMergedComparisonNumeric.check_complete
#check @MicroCFTA.SourceMergedComparisonNumeric.check_complete
