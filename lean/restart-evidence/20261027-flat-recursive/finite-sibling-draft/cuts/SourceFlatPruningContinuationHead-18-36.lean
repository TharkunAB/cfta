theorem continued_head
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (n p h target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller middleCaller : Caller width) (queries middleQueries : Queries)
    (receipt : Receipt width) (outputs : List Output)
    (observed : SourceFlatPruningCapturedEdge.run checkEmpty n p h target scs edge caller before queries =
      some receipt)
    (continued : match (generalizing := false) receipt with
      | .complete fragment reached saved after =>
          hook fragment reached saved after = .complete outputs middleCaller middleQueries
      | _ => SourceFlatPruningNativeBranches.advance receipt = some (middleCaller, middleQueries) ∧
          outputs = []) :
    run hook checkEmpty n p h target scs before (edge :: rest) caller queries =
      match run hook checkEmpty n p h target scs before rest middleCaller middleQueries with
      | .complete processed later finalCaller finalQueries =>
          .complete (receipt :: processed) (outputs ++ later) finalCaller finalQueries
      | .stopped processed later current =>
          .stopped (receipt :: processed) (outputs ++ later) current := by
