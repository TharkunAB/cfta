import MicroCFTA.SourceCurrentMemoMergeMeasured

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.MeasuredRun
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.MeasuredRun

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.MeasuredCall
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.MeasuredCall

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.MeasuredRun.erase
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.MeasuredRun.erase

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.MeasuredCall.erase
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.MeasuredCall.erase

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.of_run
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.of_run

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.of_call
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.of_call

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.SelectionReady
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.SelectionReady

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.CallSelectionReady
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.CallSelectionReady

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.run_replay
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.run_replay

#print axioms MicroCFTA.SourceCurrentMemoMergeMeasured.call_replay
#check @MicroCFTA.SourceCurrentMemoMergeMeasured.call_replay
