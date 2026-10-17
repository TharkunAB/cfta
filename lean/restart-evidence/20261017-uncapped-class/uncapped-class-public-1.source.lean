import MicroCFTA.SourceCurrentClassCallerNumeric
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentClassNumeric.complete
#print axioms MicroCFTA.SourceCurrentClassNumeric.complete

#check @MicroCFTA.SourceCurrentClassPassNumeric.fold
#print axioms MicroCFTA.SourceCurrentClassPassNumeric.fold

#check @MicroCFTA.SourceCurrentClassPassNumeric.pass
#print axioms MicroCFTA.SourceCurrentClassPassNumeric.pass

#check @MicroCFTA.SourceCurrentClassCallerNumeric.complete
#print axioms MicroCFTA.SourceCurrentClassCallerNumeric.complete
