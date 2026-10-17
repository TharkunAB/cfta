import MicroCFTA.SourceCurrentOuterActiveAncestry
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.caller
#print MicroCFTA.SourceCurrentOuterActiveAncestry.caller
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.caller

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step.node_evaluate
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step.node_evaluate
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step.node_evaluate

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step.body_rows
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step.body_rows
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step.body_rows

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step.rows_edge
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step.rows_edge
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step.rows_edge

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step.rows_tail
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step.rows_tail
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step.rows_tail

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step.descendants_children
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step.descendants_children
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step.descendants_children

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step.children_walk
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step.children_walk
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step.children_walk

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step.walk_head
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step.walk_head
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step.walk_head

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step.walk_tail
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step.walk_tail
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step.walk_tail

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Reached
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Reached
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Reached

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.refl
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.refl
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.refl

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.snoc
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.snoc
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.snoc

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.trans
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.trans
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.trans

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.protocol
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.protocol
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.protocol

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.running
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.running
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.running

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Ancestor
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Ancestor
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Ancestor

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.owners
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.owners
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.owners

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.initial_owners
#print MicroCFTA.SourceCurrentOuterActiveAncestry.initial_owners
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.initial_owners

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.busy
#print MicroCFTA.SourceCurrentOuterActiveAncestry.busy
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.busy

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.run
#print MicroCFTA.SourceCurrentOuterActiveAncestry.run
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.run

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Step.failed
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Step.failed
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Step.failed

#check @MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.failed
#print MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.failed
#print axioms MicroCFTA.SourceCurrentOuterActiveAncestry.Reached.failed

