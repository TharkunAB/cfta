import MicroCFTA.SourceCurrentRequiredRowOrigins
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

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.identity
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.identity
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.identity

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.empty
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.empty
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.empty

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.ordinary
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.ordinary
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.ordinary

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.accepted
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.accepted
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ExposureSafe.accepted

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Origin
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Origin
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Origin

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.identity
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.identity
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.identity

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.plain
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.plain
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.plain

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.ordinary
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.ordinary
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.ordinary

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap.nil
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap.nil
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap.nil

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap.cons
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap.cons
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap.cons

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap.nil
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap.nil
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap.nil

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap.cons
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap.cons
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap.cons

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap.all₂
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap.all₂
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ChildMap.all₂

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap.indexed
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap.indexed
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowMap.indexed

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.ChildrenSafe
#print MicroCFTA.SourceCurrentRequiredRowOrigins.ChildrenSafe
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.ChildrenSafe

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowsSafe
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowsSafe
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowsSafe

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.node
#print MicroCFTA.SourceCurrentRequiredRowOrigins.node
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.node

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.children
#print MicroCFTA.SourceCurrentRequiredRowOrigins.children
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.children

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.rows
#print MicroCFTA.SourceCurrentRequiredRowOrigins.rows
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.rows

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Position
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Position
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Position

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Position.child
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Position.child
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Position.child

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Position.member
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Position.member
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Position.member

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Position.body
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Position.body
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Position.body

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.root
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.root
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.root

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.child
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.child
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.child

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.member
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.member
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.member

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.body
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.body
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.body

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.annotated
#print MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.annotated
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.RowAt.annotated

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.nonplain
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.nonplain
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.nonplain

#check @MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.physical_positive
#print MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.physical_positive
#print axioms MicroCFTA.SourceCurrentRequiredRowOrigins.Origin.physical_positive
