/-- The identity hook retains the edge's native endpoint and emits no output. -/
def identityHook (_fragment : Fragment) (caller : Caller width) (queries : Queries) (_after : Cached) :
    HookResult Output Reason width :=
  .complete [] caller queries

/-- Embed a legacy branch result without continuation outputs or continuation stops. -/
def ofBranches : SourcePruningEnumerationNativeBranches.Result width → Result Output Reason width
  | .complete processed caller queries => .complete processed [] caller queries
  | .stopped processed current => .stopped processed [] (.edge current)

/-- The identity hook preserves the entire legacy result, including stopped receipts. -/
theorem identity_run
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    run (identityHook (Output := Output) (Reason := Reason)) checkEmpty r n p h k target scs before edges caller queries =
      ofBranches (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k target scs before edges caller queries) := by
