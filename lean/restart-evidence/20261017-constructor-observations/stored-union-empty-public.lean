import MicroCFTA.SourceCurrentStoredUnionEmpty
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentStoredUnionEmpty.warm
#print MicroCFTA.SourceCurrentStoredUnionEmpty.warm
#print axioms MicroCFTA.SourceCurrentStoredUnionEmpty.warm

#check @MicroCFTA.SourceCurrentStoredUnionEmpty.flatten_warm
#print MicroCFTA.SourceCurrentStoredUnionEmpty.flatten_warm
#print axioms MicroCFTA.SourceCurrentStoredUnionEmpty.flatten_warm
