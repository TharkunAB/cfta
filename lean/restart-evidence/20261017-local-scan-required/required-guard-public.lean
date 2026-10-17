import MicroCFTA.SourceCurrentRequiredGuard

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000


#print axioms MicroCFTA.SourceCurrentRequiredGuard.node
#check @MicroCFTA.SourceCurrentRequiredGuard.node
#print MicroCFTA.SourceCurrentRequiredGuard.node

#print axioms MicroCFTA.SourceCurrentRequiredGuard.children
#check @MicroCFTA.SourceCurrentRequiredGuard.children
#print MicroCFTA.SourceCurrentRequiredGuard.children

#print axioms MicroCFTA.SourceCurrentRequiredGuard.rows
#check @MicroCFTA.SourceCurrentRequiredGuard.rows
#print MicroCFTA.SourceCurrentRequiredGuard.rows

#print axioms MicroCFTA.SourceCurrentRequiredGuard.requireAll
#check @MicroCFTA.SourceCurrentRequiredGuard.requireAll
#print MicroCFTA.SourceCurrentRequiredGuard.requireAll
