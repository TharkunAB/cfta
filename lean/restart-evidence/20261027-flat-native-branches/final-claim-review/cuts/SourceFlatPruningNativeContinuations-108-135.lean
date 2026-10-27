noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h target : Nat) (scs : List Suspended) (before : Cached) :
    List (EdgeValue Symbol Constraint) → Caller width → Queries → Result Output Reason width
  | [], caller, queries => .complete [] [] caller queries
  | edge :: rest, caller, queries =>
      match SourceFlatPruningCapturedEdge.run checkEmpty nativeFuel p h target scs edge caller before queries with
      | none => .stopped [] [] (.edge none)
      | some receipt =>
          match receipt with
          | .complete fragment reached saved after =>
              match hook fragment reached saved after with
              | .stopped outputs reason endpoint =>
                  .stopped [] outputs (.continuation receipt reason endpoint)
              | .complete outputs middleCaller middleQueries =>
                  match run hook checkEmpty nativeFuel p h target scs before rest middleCaller middleQueries with
                  | .complete processed later finalCaller finalQueries =>
                      .complete (receipt :: processed) (outputs ++ later) finalCaller finalQueries
                  | .stopped processed later current =>
                      .stopped (receipt :: processed) (outputs ++ later) current
          | other =>
              match SourceFlatPruningNativeBranches.advance other with
              | none => .stopped [] [] (.edge (some other))
              | some (middleCaller, middleQueries) =>
                  match run hook checkEmpty nativeFuel p h target scs before rest middleCaller middleQueries with
                  | .complete processed outputs finalCaller finalQueries =>
                      .complete (other :: processed) outputs finalCaller finalQueries
                  | .stopped processed outputs current => .stopped (other :: processed) outputs current
