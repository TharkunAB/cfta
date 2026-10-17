import MicroCFTA.SourceCurrentRawRebuildNumeric
import MicroCFTA.SourceCurrentNodeTerminalNumeric
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentRawRebuildNumeric.edge
#print axioms MicroCFTA.SourceCurrentRawRebuildNumeric.edge
#print MicroCFTA.SourceCurrentRawRebuildNumeric.edge

#check @MicroCFTA.SourceCurrentRawRebuildNumeric.modify
#print axioms MicroCFTA.SourceCurrentRawRebuildNumeric.modify
#print MicroCFTA.SourceCurrentRawRebuildNumeric.modify

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.actual
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.actual
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.actual

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.reads
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.reads
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.reads

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.checks
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.checks
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.checks

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.post
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.post
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.post

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.available
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.available
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.available

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.frame
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.frame
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.frame

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.fits
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.fits
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.fits

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.law
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.law
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.law

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.run
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.run
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.Receipt.run

#check @MicroCFTA.SourceCurrentNodeTerminalNumeric.complete
#print axioms MicroCFTA.SourceCurrentNodeTerminalNumeric.complete
#print MicroCFTA.SourceCurrentNodeTerminalNumeric.complete
