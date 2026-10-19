import MicroCFTA.SourceCurrentClassEventPublications

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

#check @MicroCFTA.SourceCurrentClassEventPublications.Source
#print MicroCFTA.SourceCurrentClassEventPublications.Source
#print axioms MicroCFTA.SourceCurrentClassEventPublications.Source

#check @MicroCFTA.SourceCurrentClassEventPublications.Source.forget
#print MicroCFTA.SourceCurrentClassEventPublications.Source.forget
#print axioms MicroCFTA.SourceCurrentClassEventPublications.Source.forget

#check @MicroCFTA.SourceCurrentClassEventPublications.Source.later
#print MicroCFTA.SourceCurrentClassEventPublications.Source.later
#print axioms MicroCFTA.SourceCurrentClassEventPublications.Source.later

#check @MicroCFTA.SourceCurrentClassEventPublications.node
#print MicroCFTA.SourceCurrentClassEventPublications.node
#print axioms MicroCFTA.SourceCurrentClassEventPublications.node

#check @MicroCFTA.SourceCurrentClassEventPublications.children
#print MicroCFTA.SourceCurrentClassEventPublications.children
#print axioms MicroCFTA.SourceCurrentClassEventPublications.children

