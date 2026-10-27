theorem IsolatedPending.through_clear
    (held handle slot : Nat) (node : Option Nat)
    (before after : EnumerationState.State Symbol EnumGuard)
    (isolated : IsolatedPending held handle before) (different : slot ≠ held)
    (written : Success (setValue slot (.unenumerated node [])) before () after) :
    IsolatedPending held handle after := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  refine ⟨?_, ?_, EnumerationPendingReplacement.setValue_clear_incoming
    held slot node before after isolated.incoming written⟩
  · simpa only [shape] using isolated.root
  · simpa only [shape, List.getElem?_set_ne different] using isolated.stored

/-- An actual handle-only write at a different slot preserves the isolated pending certificate. -/
theorem IsolatedPending.through_handle_write
    (held handle slot : Nat) (oldNode newNode : Option Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard)
    (isolated : IsolatedPending held handle before) (different : slot ≠ held)
    (stored : before.values[slot]? = some (.unenumerated oldNode scs))
    (written : Success (setValue slot (.unenumerated newNode scs)) before () after) :
    IsolatedPending held handle after := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  refine ⟨?_, ?_, EnumerationPendingReplacement.setValue_incoming
    held slot oldNode newNode scs before after stored isolated.incoming written⟩
  · simpa only [shape] using isolated.root
  · simpa only [shape, List.getElem?_set_ne different] using isolated.stored

/-- An actual value read preserves the isolated pending certificate. -/
theorem IsolatedPending.through_getValue
    (held handle fuel uv : Nat) (value : UVarValue Symbol)
    (before after : EnumerationState.State Symbol EnumGuard)
    (isolated : IsolatedPending held handle before)
    (total : UnionFind.Total before.representatives)
    (observed : Success (getValue fuel uv) before value after) : IsolatedPending held handle after :=
  isolated.through_frame (getValue_frame fuel uv before after value total observed).1

/-- An actual recursion check at a different selected root preserves isolation in both branches. -/
theorem IsolatedPending.through_checkRepeated
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (held heldHandle fuel uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard) (repeated : Bool)
    (isolated : IsolatedPending held heldHandle before)
    (ready : EnumerationDriver.Ready uv before) (different : uv ≠ held)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) : IsolatedPending held heldHandle after := by
  cases repeated with
  | false =>
      exact isolated.through_frame
        (SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame heap fuel uv handle scs
          before after ready.safe.1.total observed)
  | true =>
      cases decoded : lookupNode heap handle with
      | none =>
          have impossible : Success (failure .unresolvedReference) before true after := by
            simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
          exact (success_failure .unresolvedReference before after true impossible).elim
      | some value =>
          by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
          · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
            obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
            obtain ⟨same, _safe, _counter, _protected⟩ := EnumerationDriver.representative_root fuel uv root
              before resolved ready.safe ready.inside ready.root resolution
            subst root
            have frame := representative_frame fuel uv uv before resolved ready.safe.1.total resolution
            have resolvedIsolated := isolated.through_frame frame
            obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
            obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
            subst current currentState
            by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry uv
            · simp only [seen, ↓reduceIte] at continued
              obtain ⟨token, cleared, written, returned⟩ := (success_bind _ _ _ _ _).mp continued
              cases token
              obtain ⟨_same, afterSame⟩ := (success_pure true true cleared after).mp returned
              subst after
              exact resolvedIsolated.through_clear held heldHandle uv (some handle) resolved cleared
                different written
            · have impossible : Success (pure false) resolved true after := by
                simpa only [seen, ↓reduceIte] using continued
              obtain ⟨impossible, _same⟩ := (success_pure false true resolved after).mp impossible
              cases impossible
          · have impossible : Success (pure false) before true after := by
              simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
                Bool.false_eq_true, ↓reduceIte] using observed
            obtain ⟨impossible, _same⟩ := (success_pure false true before after).mp impossible
            cases impossible

section Prepared
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Typing Key : Type}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The actual nonempty prepared action preserves an isolated different root. -/
theorem IsolatedPending.through_prepared_nonempty
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Constraint → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (held heldHandle nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Value Symbol Constraint)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit)
    (checked after : EnumerationState.State Symbol Constraint)
    (isolated : IsolatedPending held heldHandle checked)
    (total : UnionFind.Total checked.representatives) (root : IsRoot checked.representatives uv)
    (different : uv ≠ held)
    (stored : checked.values[uv]? = some (.unenumerated (some oldHandle) scs))
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) : IsolatedPending held heldHandle after := by
  have actual := SourcePruningEnumerationSelectedStep.prepared_action holeKey fits admits metadata
    nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value heap nextHeap
    narrowed nonempty encoded
  rw [prepared] at actual
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actual).1).2
  rw [actionSame] at observed
  by_cases same : newHandle = oldHandle
  · rw [ite_eq_left same] at observed
    obtain ⟨_same, afterSame⟩ := (success_pure () () checked after).mp observed
    simpa only [afterSame] using isolated
  · rw [ite_eq_right same] at observed
    obtain ⟨selected, resolved, reading, writing⟩ := (success_bind _ _ _ _ _).mp observed
    have frame := representative_frame representativeFuel uv selected checked resolved total reading
    obtain ⟨found, foundLookup, selectedRoot, _endpoint⟩ :=
      (representative_success representativeFuel uv checked resolved selected).mp reading
    have selectedIsUv : selected = uv := by
      rw [selectedRoot]
      exact (UnionFind.reaches_unique
        (UnionFind.findRoot_correct representativeFuel checked.representatives uv found foundLookup).1
        root.choose_spec).1
    rw [selectedIsUv] at writing
    have resolvedStored : resolved.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
      simpa only [frame.values] using stored
    exact (isolated.through_frame frame).through_handle_write held heldHandle uv
      (some oldHandle) (some newHandle) scs resolved after different resolvedStored writing

end Prepared
end MicroCFTA.EnumerationDischargeHistory
