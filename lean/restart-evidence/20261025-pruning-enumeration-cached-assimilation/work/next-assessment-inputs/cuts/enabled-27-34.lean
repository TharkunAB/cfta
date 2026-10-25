noncomputable def check
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (p h : Nat) (query : Node) (before : Checked width) (memo : Fourth)
    (queries : Queries) : SourceCurrentAllocatedConjunctionWorker.Outcome width × Queries :=
  let guardResult : Bool × Queries := SourceEndpointMemo.run query queries
  if guardResult.1 then
    (SourceCurrentAllocatedConjunctionWorker.call p h 1000 query before memo, guardResult.2)
  else (.done false before memo, guardResult.2)
