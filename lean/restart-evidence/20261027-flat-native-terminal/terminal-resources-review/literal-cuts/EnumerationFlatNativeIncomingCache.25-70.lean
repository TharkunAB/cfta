def adapt
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (target : Nat) (incomingScs : List EnumerationState.Suspended)
    (before : EnumerationFlatCached.Cached Symbol Constraint)
    (read : EnumerationFlatState.State Symbol Constraint) (raw : Raw) :
    Option (EnumerationFlatCached.Cached Symbol Constraint) :=
  match raw with
  | [] =>
      match read.values[target]? with
      | some (.unenumerated _oldNode oldScs) =>
        let value : EnumerationState.UVarValue Symbol :=
          .unenumerated (some 0) (incomingScs ++ oldScs)
        let core : EnumerationFlatState.State Symbol Constraint :=
          {read with
            values := read.values.set target value
            recursionAncestry := fun other => if other = target then
              (read.expansionAncestry ++ read.recursionAncestry target).eraseDups
              else read.recursionAncestry other}
        (EnumerationFlatNativeIndex.write heap target value incomingScs []
          (EnumerationFlatCached.frame read before)).map (EnumerationFlatCached.frame core)
      | _ => none
  | [.ok ((), returned)] =>
      (returned.values[target]?).bind fun slotValue =>
        (EnumerationFlatNativeIndex.write heap target slotValue incomingScs []
          (EnumerationFlatCached.frame read before)).map (EnumerationFlatCached.frame returned)
  | _ => none

/-- Retain one original observation and attach its optional cache candidate. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationFlatCached.Cached Symbol Constraint)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    ((Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width) (Option Raw)) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint) ×
      Option (EnumerationFlatCached.Cached Symbol Constraint) :=
  let observed : (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width) (Option Raw)) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint :=
    EnumerationFlatNativeIncoming.run checkEmpty nativeFuel p h
      beforeCaller before.core target incoming incomingScs queries
  (observed, match observed with
    | (.ok (some raw), reachedCaller, _savedQueries, read) =>
        adapt reachedCaller.checked.native.machine.heap target incomingScs before read raw
    | _ => none)
