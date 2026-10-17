import MicroCFTA.SourceCurrentAllocatedReaderConsumed

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.SourceCurrentAllocatedReaderConsumed.emitted
#check @MicroCFTA.SourceCurrentAllocatedReaderConsumed.emitted

#print axioms MicroCFTA.SourceCurrentAllocatedReaderConsumed.Path
#check @MicroCFTA.SourceCurrentAllocatedReaderConsumed.Path

#print axioms MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run
#check @MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run

#print axioms MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run.path
#check @MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run.path

#print axioms MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run.pending_empty
#check @MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run.pending_empty

#print axioms MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run.exact
#check @MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run.exact

#print axioms MicroCFTA.SourceCurrentAllocatedReaderConsumed.extract
#check @MicroCFTA.SourceCurrentAllocatedReaderConsumed.extract

#print axioms MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run.stable
#check @MicroCFTA.SourceCurrentAllocatedReaderConsumed.Run.stable
