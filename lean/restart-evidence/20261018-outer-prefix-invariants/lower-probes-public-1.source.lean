import MicroCFTA.SourceCurrentLowerProbeHeap

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentLowerProbeHeap.Good
#print MicroCFTA.SourceCurrentLowerProbeHeap.Good
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.Good

#check @MicroCFTA.SourceCurrentLowerProbeHeap.Good.physical
#print MicroCFTA.SourceCurrentLowerProbeHeap.Good.physical
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.Good.physical

#check @MicroCFTA.SourceCurrentLowerProbeHeap.Good.advance
#print MicroCFTA.SourceCurrentLowerProbeHeap.Good.advance
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.Good.advance

#check @MicroCFTA.SourceCurrentLowerProbeHeap.Effect
#print MicroCFTA.SourceCurrentLowerProbeHeap.Effect
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.Effect

#check @MicroCFTA.SourceCurrentLowerProbeHeap.Effect.refl
#print MicroCFTA.SourceCurrentLowerProbeHeap.Effect.refl
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.Effect.refl

#check @MicroCFTA.SourceCurrentLowerProbeHeap.Effect.trans
#print MicroCFTA.SourceCurrentLowerProbeHeap.Effect.trans
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.Effect.trans

#check @MicroCFTA.SourceCurrentLowerProbeHeap.operand
#print MicroCFTA.SourceCurrentLowerProbeHeap.operand
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.operand

#check @MicroCFTA.SourceCurrentLowerProbeHeap.target
#print MicroCFTA.SourceCurrentLowerProbeHeap.target
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.target

#check @MicroCFTA.SourceCurrentLowerProbeHeap.SharedGood
#print MicroCFTA.SourceCurrentLowerProbeHeap.SharedGood
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.SharedGood

#check @MicroCFTA.SourceCurrentLowerProbeHeap.SharedGood.initial
#print MicroCFTA.SourceCurrentLowerProbeHeap.SharedGood.initial
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.SharedGood.initial

#check @MicroCFTA.SourceCurrentLowerProbeHeap.force
#print MicroCFTA.SourceCurrentLowerProbeHeap.force
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.force

#check @MicroCFTA.SourceCurrentLowerProbeHeap.leaf
#print MicroCFTA.SourceCurrentLowerProbeHeap.leaf
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.leaf

#check @MicroCFTA.SourceCurrentLowerProbeHeap.edit
#print MicroCFTA.SourceCurrentLowerProbeHeap.edit
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.edit

#check @MicroCFTA.SourceCurrentLowerProbeHeap.edit_list
#print MicroCFTA.SourceCurrentLowerProbeHeap.edit_list
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.edit_list

#check @MicroCFTA.SourceCurrentLowerProbeHeap.run_class
#print MicroCFTA.SourceCurrentLowerProbeHeap.run_class
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.run_class

#check @MicroCFTA.SourceCurrentLowerProbeHeap.class_fold
#print MicroCFTA.SourceCurrentLowerProbeHeap.class_fold
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.class_fold

#check @MicroCFTA.SourceCurrentLowerProbeHeap.class_pass
#print MicroCFTA.SourceCurrentLowerProbeHeap.class_pass
#print axioms MicroCFTA.SourceCurrentLowerProbeHeap.class_pass
