private theorem retained_action_success
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (fuel uv oldHandle : Nat) (scs : List Suspended) (oldValue value : Node)
    (caller reached : Caller width) (before after : Cached) (queries : SourceEndpointMemo.Memos)
    (readAfter checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (selectedAction : EnumerateM Symbol Constraint Unit)
    (preparedField : MergedSourceComparison.Result Symbol Constraint
      (Node × Option (EnumerateM Symbol Constraint Unit)))
    (right : Option (List (Except Error ((Bool × Metadata Typing) × Core))))
    (ordinary : Option (List (Except Error ((Nat × Nat × List Suspended × Node) × Core)) ×
      Option (SourcePruningEnumerationNativeBranches.Result width)))
    (reading : ExceptT.run (getValue fuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap fuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel uv oldHandle
      scs oldValue caller.checked.native.machine.heap = .done (value, some selectedAction) heap)
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before queries = .narrowed checked preparedField reached queries
        (some [.ok ((), after.core)]) (some after) right ordinary) :
    Success selectedAction checked () after.core := by
  simp only [runPrefix, reading, checking, decoded, prepared] at actual
  cases rawEq : ExceptT.run (selectedAction checked) with
  | nil => simp only [rawEq] at actual; cases actual
  | cons first rest =>
      cases first with
      | error fault => simp only [rawEq] at actual; cases actual
      | ok pair =>
          obtain ⟨token, observed⟩ := pair
          cases token
          cases rest with
          | cons _ _ => simp only [rawEq] at actual; cases actual
          | nil =>
              simp only [rawEq] at actual
              cases encoded : encodeNode value with
              | none => simp only [encoded] at actual; cases actual
              | some newHandle =>
                  simp only [encoded] at actual
                  cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle
                      scs before observed with
                  | none => simp only [adapted] at actual; cases actual
                  | some attached =>
                      have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel
                          metadata uv (.inr newHandle) attached.core) = [.ok ((false, metadata), attached.core)] := by
                        rw [SourcePruningRecordTypes.recordTypes_inr]
                        rfl
                      simp only [adapted, recorded] at actual
                      have ⟨_checked, _prepared, _caller, _queries, actionSame, _candidate, _right, _ordinary⟩ :=
                        Result.narrowed.inj actual
                      have coreSame : observed = after.core := by
                        simpa only [Option.some.injEq, List.cons.injEq, Except.ok.injEq, Prod.mk.injEq,
                          true_and, and_true] using actionSame
                      rw [Success, ← coreSame, rawEq]
                      exact List.mem_singleton_self _


variable [DecidableEq Symbol] [DecidableEq Node]

private theorem finish_cache_fields
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (uv : Nat) (observed : Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ => finish checkEmpty edgesOf 0 0 0 0 0 uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, finish checkEmpty edgesOf 0 0 0 0 0 uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold finish
      split <;> simp_all only [Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩
