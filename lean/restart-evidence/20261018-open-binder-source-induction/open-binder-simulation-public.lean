import MicroCFTA.SourceCurrentOpenPreorderSimulation
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

#check @MicroCFTA.SourceCurrentOpenPreorderSimulation.Mutual
#print MicroCFTA.SourceCurrentOpenPreorderSimulation.Mutual
#print axioms MicroCFTA.SourceCurrentOpenPreorderSimulation.Mutual

#check @MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed
#print MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed
#print axioms MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed

#check @MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed.path
#print MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed.path
#print axioms MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed.path

#check @MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed.reference
#print MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed.reference
#print axioms MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed.reference

#check @MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed.row
#print MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed.row
#print axioms MicroCFTA.SourceCurrentOpenPreorderSimulation.Directed.row

#check @MicroCFTA.SourceCurrentOpenPreorderSimulation.same
#print MicroCFTA.SourceCurrentOpenPreorderSimulation.same
#print axioms MicroCFTA.SourceCurrentOpenPreorderSimulation.same

#check @MicroCFTA.SourceCurrentOpenPreorderSimulation.related
#print MicroCFTA.SourceCurrentOpenPreorderSimulation.related
#print axioms MicroCFTA.SourceCurrentOpenPreorderSimulation.related
