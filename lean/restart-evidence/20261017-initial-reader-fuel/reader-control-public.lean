import MicroCFTA.SourceCurrentAllocatedReaderControl
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Config
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Config

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Good
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Good

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Fits
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Fits

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.measure
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.measure

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.g
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.g

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.g_strict
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.g_strict

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.g_mono
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.g_mono

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.weight_le_mass
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.weight_le_mass

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.workWeight_le_mass
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.workWeight_le_mass

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Fits.mono
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Fits.mono

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.initialBound
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.initialBound

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.initial_fits
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.initial_fits

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.measure_le
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.measure_le

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.good
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.good

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.fits
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.fits

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.decreases
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.decreases

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.empty
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.empty

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.node
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.node

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.union_seen
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.union_seen

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.union_fresh
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.union_fresh

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.mu_seen
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.mu_seen

#print axioms MicroCFTA.SourceCurrentAllocatedReaderControl.Step.mu_fresh
#check @MicroCFTA.SourceCurrentAllocatedReaderControl.Step.mu_fresh
