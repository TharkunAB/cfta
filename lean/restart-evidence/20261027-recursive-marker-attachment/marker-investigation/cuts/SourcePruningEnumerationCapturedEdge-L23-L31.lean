
/-- Finalize each successful selected edge at the original captured raw slot. -/
noncomputable def run (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries) : Option (Result width) :=
  match SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | .complete fragment afterCaller saved after =>
      (SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap k target fragment after).map
        (fun finished => .complete fragment afterCaller saved finished)
