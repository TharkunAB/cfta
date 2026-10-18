import MicroCFTA.SourceCurrentDirectedClosure
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentDirectedClosure.Closure
#print MicroCFTA.SourceCurrentDirectedClosure.Closure
#print axioms MicroCFTA.SourceCurrentDirectedClosure.Closure

#check @MicroCFTA.SourceCurrentDirectedClosure.Closure.refl
#print MicroCFTA.SourceCurrentDirectedClosure.Closure.refl
#print axioms MicroCFTA.SourceCurrentDirectedClosure.Closure.refl

#check @MicroCFTA.SourceCurrentDirectedClosure.Closure.step
#print MicroCFTA.SourceCurrentDirectedClosure.Closure.step
#print axioms MicroCFTA.SourceCurrentDirectedClosure.Closure.step

#check @MicroCFTA.SourceCurrentDirectedClosure.Closure.single
#print MicroCFTA.SourceCurrentDirectedClosure.Closure.single
#print axioms MicroCFTA.SourceCurrentDirectedClosure.Closure.single

#check @MicroCFTA.SourceCurrentDirectedClosure.Closure.trans
#print MicroCFTA.SourceCurrentDirectedClosure.Closure.trans
#print axioms MicroCFTA.SourceCurrentDirectedClosure.Closure.trans

#check @MicroCFTA.SourceCurrentDirectedClosure.Closure.mono
#print MicroCFTA.SourceCurrentDirectedClosure.Closure.mono
#print axioms MicroCFTA.SourceCurrentDirectedClosure.Closure.mono

#check @MicroCFTA.SourceCurrentDirectedClosure.or_directed
#print MicroCFTA.SourceCurrentDirectedClosure.or_directed
#print axioms MicroCFTA.SourceCurrentDirectedClosure.or_directed

#check @MicroCFTA.SourceCurrentDirectedClosure.directed
#print MicroCFTA.SourceCurrentDirectedClosure.directed
#print axioms MicroCFTA.SourceCurrentDirectedClosure.directed

