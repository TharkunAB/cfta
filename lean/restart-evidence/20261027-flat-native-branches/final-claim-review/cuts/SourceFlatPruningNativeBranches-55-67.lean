noncomputable def run (checkEmpty : Bool) (nativeFuel p h target : Nat) (scs : List Suspended)
    (before : Cached) : List (EdgeValue Symbol Constraint) → Caller width → Queries → Result width
  | [], caller, queries => .complete [] caller queries
  | edge :: rest, caller, queries =>
      match SourceFlatPruningCapturedEdge.run checkEmpty nativeFuel p h target scs edge caller before queries with
      | none => .stopped [] none
      | some receipt =>
          match advance receipt with
          | none => .stopped [] (some receipt)
          | some (middleCaller, middleQueries) =>
              match run checkEmpty nativeFuel p h target scs before rest middleCaller middleQueries with
              | .complete processed afterCaller saved => .complete (receipt :: processed) afterCaller saved
              | .stopped processed current => .stopped (receipt :: processed) current
