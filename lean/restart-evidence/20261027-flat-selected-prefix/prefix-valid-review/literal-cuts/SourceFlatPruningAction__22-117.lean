/-- Narrow once and retain the native value beside its actual flat action. -/
def prepare [DecidableEq (EdgeKey Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol NativeGuard → Bool) (metadata : Metadata Typing)
    (nativeFuel uv oldHandle : Nat) (scs : List Suspended) (oldValue : Value Symbol NativeGuard)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) :
    MergedSourceComparison.Result Symbol NativeGuard
      (Value Symbol NativeGuard × Option (Action Symbol EnumGuard Unit)) :=
  match SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap with
  | .failed fault after => .failed fault after
  | .done result nextHeap =>
      .done (result,
        match result with
        | .empty => some EnumerationFlatState.reject
        | _ =>
            match encodeNode result with
            | none => none
            | some newHandle => some (
                if newHandle = oldHandle then pure ()
                else EnumerationFlatState.representative uv >>= fun selected =>
                  EnumerationFlatState.setValue selected (.unenumerated (some newHandle) scs))) nextHeap

/-- Retain native effects and compare all captured rows at the actual entry cores. -/
def PreparedRelated (flatCore : EnumerationFlatState.State Symbol EnumGuard)
    (earlierCore : EnumerationState.State Symbol EnumGuard)
    (flat : MergedSourceComparison.Result Symbol NativeGuard
      (Value Symbol NativeGuard × Option (Action Symbol EnumGuard Unit)))
    (earlier : MergedSourceComparison.Result Symbol NativeGuard
      (Value Symbol NativeGuard × Option (EnumerateM Symbol EnumGuard Unit))) : Prop :=
  flat.state = earlier.state ∧
    match flat, earlier with
    | .failed first _, .failed second _ => first = second
    | .done (value, first) _, .done (oldValue, second) _ =>
        value = oldValue ∧ match first, second with
        | none, none => True
        | some action, some oldAction => Results Related (action flatCore) (oldAction earlierCore)
        | _, _ => False
    | _, _ => False

private theorem replacement_related (related : Related flat earlier)
    (uv oldHandle newHandle : Nat) (scs : List Suspended)
    (completed : UnionFind.findRoot fuel earlier.representatives uv = some found) :
    Results Related
      ((if newHandle = oldHandle then (pure () : Action Symbol EnumGuard Unit)
        else EnumerationFlatState.representative uv >>= fun root =>
          EnumerationFlatState.setValue root (.unenumerated (some newHandle) scs)) flat)
      ((if newHandle = oldHandle then (pure () : EnumerateM Symbol EnumGuard Unit)
        else EnumerationState.representative fuel uv >>= fun root =>
          EnumerationState.setValue root (.unenumerated (some newHandle) scs)) earlier) := by
  by_cases same : newHandle = oldHandle
  · simp only [same, ↓reduceIte]
    exact pure_related related ()
  · simp only [same, ↓reduceIte]
    apply stateT_bind _ _ _ _ (representative_related related completed)
    intro root left right states
    exact setValue_related states root (.unenumerated (some newHandle) scs)

/-- Completed old representative reads preserve every native and action outcome. -/
theorem prepare_related [DecidableEq (EdgeKey Symbol NativeGuard)]
    (related : Related flat earlier)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol NativeGuard → Bool) (metadata : Metadata Typing)
    (nativeFuel uv oldHandle : Nat) (scs : List Suspended) (oldValue : Value Symbol NativeGuard)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (completed : UnionFind.findRoot fuel earlier.representatives uv = some found) :
    PreparedRelated flat earlier
      (prepare holeKey fits admits metadata nativeFuel uv oldHandle scs oldValue heap)
      (SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel fuel uv oldHandle scs oldValue heap) := by
  unfold prepare SourcePruningEnumerationAction.prepare
  cases observed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap with
  | failed fault after => exact ⟨rfl, rfl⟩
  | done result after =>
      cases result with
      | empty => exact ⟨rfl, rfl, .nil⟩
      | reference name => exact ⟨rfl, rfl, trivial⟩
      | node entry edges depth free =>
          exact ⟨rfl, rfl, replacement_related related uv oldHandle (entry.identity + 1) scs completed⟩
      | union entry members depth free =>
          exact ⟨rfl, rfl, replacement_related related uv oldHandle (entry.identity + 1) scs completed⟩
      | mu entry body depth ordinary =>
          exact ⟨rfl, rfl, replacement_related related uv oldHandle (entry.identity + 1) scs completed⟩

/-- One old action-read bound covers every native bound at the same actual entry. -/
theorem prepare_stable [DecidableEq (EdgeKey Symbol NativeGuard)]
    (related : Related flat earlier)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol NativeGuard → Bool) (metadata : Metadata Typing)
    (uv oldHandle : Nat) (scs : List Suspended) (oldValue : Value Symbol NativeGuard)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) :
    ∃ fuel, ∀ extra nativeFuel, PreparedRelated flat earlier
      (prepare holeKey fits admits metadata nativeFuel uv oldHandle scs oldValue heap)
      (SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel (fuel + extra)
        uv oldHandle scs oldValue heap) := by
  obtain ⟨fuel, found, stable, _path, _size, _forest⟩ := FlatUnionFind.find_stable related.representatives uv
  exact ⟨fuel, fun extra nativeFuel => prepare_related related holeKey fits admits metadata
    nativeFuel uv oldHandle scs oldValue heap (stable extra)⟩
