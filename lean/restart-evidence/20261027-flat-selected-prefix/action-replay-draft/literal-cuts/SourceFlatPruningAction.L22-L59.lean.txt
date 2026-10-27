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
