import MicroCFTA.SourceCurrentGateFrameResources
import MicroCFTA.SourceCurrentSeededCallerNumeric
import MicroCFTA.SourceCurrentConjunctionAlphabetBounds
import MicroCFTA.SourceCurrentAllocatedScanWorkerActual
import MicroCFTA.SourceCurrentNativeGuardAlphabet
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentGateFrameResources.primary

#check @MicroCFTA.SourceCurrentGateFrameResources.secondary

#check @MicroCFTA.SourceCurrentAllocatedPrimaryReads.lift_class

#check @MicroCFTA.SourceCurrentSecondaryMemos.lift_class

#check @MicroCFTA.SourceCurrentSecondaryProjectionScoped.class_support

#check @MicroCFTA.SourceCurrentSeededCallerNumeric.complete

#check @MicroCFTA.SourceCurrentConjunctionAlphabetBounds.caller_complete

#check @MicroCFTA.SourceCurrentAllocatedConjunctionCaller.actual

#check @MicroCFTA.SourceCurrentConjunctionQueryGlobalMemos.QueryReads.run

#check @MicroCFTA.SourceCurrentAllocatedScanSourceReads.ScanReads.continued

#check @MicroCFTA.SourceCurrentAllocatedPartialInvariant.Post.trans

#check @MicroCFTA.SourceCurrentAllocatedScanWorker.scan

#check @MicroCFTA.SourceCurrentAllocatedScanWorkerStability.scan_done_stable

#check @MicroCFTA.SourceCurrentAllocatedScanWorkerCompletion.scan_complete

#check @MicroCFTA.SourceCurrentConjunctionClassScanCompletion.finite

#check @MicroCFTA.SourceCurrentAllocatedScanCaller.actual

#check @MicroCFTA.SourceCurrentAllocatedQueryMemo.physical_advance

#check @MicroCFTA.SourceCurrentAllocatedQueryMemo.advance_tables

#check @MicroCFTA.SourceCurrentNativeGuardAlphabet.advance_step

#check @MicroCFTA.SourceCurrentNativeGuardAlphabet.advance_count_mono
