import MicroCFTA.SourceCurrentAllocatedReaderHistory

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

#print axioms MicroCFTA.SourceCurrentAllocatedReaderHistory.Run.history
#check @MicroCFTA.SourceCurrentAllocatedReaderHistory.Run.history

#print axioms MicroCFTA.SourceCurrentAllocatedReaderHistory.collect_history
#check @MicroCFTA.SourceCurrentAllocatedReaderHistory.collect_history

#print axioms MicroCFTA.SourceCurrentAllocatedReaderHistory.nodeEdges_history
#check @MicroCFTA.SourceCurrentAllocatedReaderHistory.nodeEdges_history

#print axioms MicroCFTA.SourceCurrentAllocatedReaderHistory.read_history
#check @MicroCFTA.SourceCurrentAllocatedReaderHistory.read_history
