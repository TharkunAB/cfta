import MicroCFTA.IntersectNumericFuel

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

#print axioms MicroCFTA.IntersectSchedule.call_numeric
#check @MicroCFTA.IntersectSchedule.call_numeric
#print axioms MicroCFTA.IntersectSchedule.requiredFuel_le_numeric
#check @MicroCFTA.IntersectSchedule.requiredFuel_le_numeric
