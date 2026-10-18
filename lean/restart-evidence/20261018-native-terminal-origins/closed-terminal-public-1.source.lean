import MicroCFTA.SourceCurrentNativeQueryClosedTerminal

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

#check @MicroCFTA.SourceCurrentNativeQueryClosedTerminal.route_closed
#print MicroCFTA.SourceCurrentNativeQueryClosedTerminal.route_closed
#print axioms MicroCFTA.SourceCurrentNativeQueryClosedTerminal.route_closed

#check @MicroCFTA.SourceCurrentNativeQueryClosedTerminal.closed_residual
#print MicroCFTA.SourceCurrentNativeQueryClosedTerminal.closed_residual
#print axioms MicroCFTA.SourceCurrentNativeQueryClosedTerminal.closed_residual

