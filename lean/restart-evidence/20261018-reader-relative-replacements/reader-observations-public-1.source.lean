import MicroCFTA.SourceCurrentReaderObservations

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentReaderObservations.Related
#print MicroCFTA.SourceCurrentReaderObservations.Related
#print axioms MicroCFTA.SourceCurrentReaderObservations.Related
#check @MicroCFTA.SourceCurrentReaderObservations.Related.refl
#print MicroCFTA.SourceCurrentReaderObservations.Related.refl
#print axioms MicroCFTA.SourceCurrentReaderObservations.Related.refl
#check @MicroCFTA.SourceCurrentReaderObservations.Related.symm
#print MicroCFTA.SourceCurrentReaderObservations.Related.symm
#print axioms MicroCFTA.SourceCurrentReaderObservations.Related.symm
#check @MicroCFTA.SourceCurrentReaderObservations.Related.trans
#print MicroCFTA.SourceCurrentReaderObservations.Related.trans
#print axioms MicroCFTA.SourceCurrentReaderObservations.Related.trans
#check @MicroCFTA.SourceCurrentReaderObservations.of_uniform
#print MicroCFTA.SourceCurrentReaderObservations.of_uniform
#print axioms MicroCFTA.SourceCurrentReaderObservations.of_uniform
#check @MicroCFTA.SourceCurrentReaderObservations.makeNode
#print MicroCFTA.SourceCurrentReaderObservations.makeNode
#print axioms MicroCFTA.SourceCurrentReaderObservations.makeNode
#check @MicroCFTA.SourceCurrentReaderObservations.makeUnion
#print MicroCFTA.SourceCurrentReaderObservations.makeUnion
#print axioms MicroCFTA.SourceCurrentReaderObservations.makeUnion
