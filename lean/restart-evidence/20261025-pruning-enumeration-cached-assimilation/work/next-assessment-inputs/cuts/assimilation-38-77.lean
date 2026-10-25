theorem pending_assimilation_complete
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (nativeBefore : SourceEqualityNativeDemand.State width)
    (before : EnumerationState.State Symbol EnumGuard)
    (source target sourceHandle targetHandle : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (ready : SourceCurrentConjunctionClassScan.Ready nativeBefore)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory nativeBefore)
    (memos : EndpointMemoGateTrace.Memos)
    (globals : EndpointMemoGateTrace.Valid nativeBefore.native.machine.heap memos)
    (realized : PendingRealized nativeBefore.native.machine.heap before)
    (sourceStored : before.values[source]? = some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated (some targetHandle) targetScs))
    (different : target ≠ source)
    (ranges : match lookupNode nativeBefore.native.machine.heap sourceHandle,
        lookupNode nativeBefore.native.machine.heap targetHandle with
      | some left, some right => SourceCurrentAllocatedNativeRequestBounds.WordRanges
          (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) nativeBefore
      | _, _ => True) :
    ∃ (left right : InternedConstructorTemplates.Value Symbol Constraint)
      (next : SourceCurrentAllocatedNativeInventoryState.Inventory)
      (result : InternedConstructorTemplates.Value Symbol Constraint)
      (nativeAfter : SourceEqualityNativeDemand.State width) (resultHandle : Nat),
      lookupNode nativeBefore.native.machine.heap sourceHandle = some left ∧
      lookupNode nativeBefore.native.machine.heap targetHandle = some right ∧
      next.source = nativeBefore.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right nativeBefore result nativeAfter memos ∧
      encodeNode result = some resultHandle ∧ lookupNode nativeAfter.native.machine.heap resultHandle = some result ∧
      (result = .empty →
        ExceptT.run (finish (EnumGuard := EnumGuard) source target resultHandle sourceScs targetScs result before) = []) ∧
      (result ≠ .empty → ∃ after : EnumerationState.State Symbol EnumGuard,
        ExceptT.run (finish (EnumGuard := EnumGuard) source target resultHandle sourceScs targetScs result before) =
          [.ok ((), after)] ∧
        after = assimilated before target source (.unenumerated (some resultHandle) (sourceScs ++ targetScs)) ∧
        after.values[target]? = some (.unenumerated (some resultHandle) (sourceScs ++ targetScs)) ∧
        after.values[source]? = some .eliminated ∧
        PendingRealized nativeAfter.native.machine.heap after) := by
