def Valid
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv : Nat)
    (caller : Caller width) (before : Cached) (memos : Memos) : Result width Typing → Prop := fun result =>
  ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
    ExceptT.run (getValue readFuel uv before.core) = [.ok (.unenumerated (some oldHandle) scs, readAfter)] ∧
    match result with
    | .stopped _ _ => False
    | .parked checked candidate raw =>
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          checkFuel uv oldHandle scs readAfter) = [.ok (true, checked)] ∧
        ∃ after : Cached, candidate = some after ∧ after.core = checked ∧
          SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after ∧ Safe after.core ∧
          EnumerationReferences.PendingReferences after.core ∧ after.core.counter = before.core.counter ∧
          (∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
            EnumerationOrder.Stratified after.core level frontier) ∧
          raw = some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata after checked))
    | .narrowed checked prepared reached queries action candidate right ordinary =>
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)] ∧
        ∃ (oldValue value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
