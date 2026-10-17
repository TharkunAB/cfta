import MicroCFTA.SourceCurrentAllocatedUnfoldHistory

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Good
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Good

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Fits
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Fits

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Event
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Event

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History.trans
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History.trans

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Event.good
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Event.good

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Event.fits
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Event.fits

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Event.progress
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.Event.progress

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.measure
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.measure

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.measure_le
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.measure_le

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History.path_control
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History.path_control

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History.bound
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History.bound

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.initialBound
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.initialBound

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.heapBound
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.heapBound

#print axioms MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History.complete
#check @MicroCFTA.SourceCurrentAllocatedUnfoldHistory.History.complete
