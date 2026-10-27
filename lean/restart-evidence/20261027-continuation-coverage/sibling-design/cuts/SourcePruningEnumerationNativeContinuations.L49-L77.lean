  | edge :: rest, caller, queries =>
      match SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => .stopped [] [] (.edge none)
      | some receipt =>
          match receipt with
          | .complete fragment reached saved after =>
              match hook fragment reached saved after with
              | .stopped outputs reason endpoint =>
                  .stopped [] outputs (.continuation receipt reason endpoint)
              | .complete outputs middleCaller middleQueries =>
                  match run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries with
                  | .complete processed later finalCaller finalQueries =>
                      .complete (receipt :: processed) (outputs ++ later) finalCaller finalQueries
                  | .stopped processed later current =>
                      .stopped (receipt :: processed) (outputs ++ later) current
          | other =>
              match SourcePruningEnumerationNativeBranches.advance other with
              | none => .stopped [] [] (.edge (some other))
              | some (middleCaller, middleQueries) =>
                  match run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries with
                  | .complete processed outputs finalCaller finalQueries =>
                      .complete (other :: processed) outputs finalCaller finalQueries
                  | .stopped processed outputs current => .stopped (other :: processed) outputs current

/-- A missing edge result retains its absence and does not invoke the hook or suffix. -/
theorem missing
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
