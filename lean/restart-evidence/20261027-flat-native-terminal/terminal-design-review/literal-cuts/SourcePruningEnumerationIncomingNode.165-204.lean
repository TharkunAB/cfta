          | none => True
      | _ => True) :
    ∃ (r n p h : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
      (read after : EnumerationState.State Symbol EnumGuard) (afterCaller : Caller width)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (replacement : Node) (handle : Nat),
      (∀ extra, ExceptT.run (getValue (r + extra) uv before) =
        [.ok (.unenumerated oldNode oldScs, read)]) ∧
      EnumerationCompressionFrame.Frame before read ∧
      (∀ extra extraNative P H, p ≤ P → h ≤ H →
        run checkEmpty (r + extra) (n + extraNative) P H beforeCaller before uv incoming incomingScs memos.query =
          (.ok (some (if replacement = .empty then [] else [.ok ((), after)])),
            afterCaller, savedQueries, read)) ∧
      ExceptT.run ((do
        setValue uv (.unenumerated (some handle) (incomingScs ++ oldScs))
        inheritAncestry uv) read) = [.ok ((), after)] ∧
      after = {read with
        values := read.values.set uv (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = uv then
          (read.expansionAncestry ++ read.recursionAncestry uv).eraseDups else read.recursionAncestry other} ∧
      after.values[uv]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      StorageValid after ∧ PendingRealized afterCaller.checked.native.machine.heap after ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      Cache.Extends memos.unfolding final.unfolding ∧
      Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
      encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
      (oldNode = none → replacement = incoming ∧ afterCaller = beforeCaller ∧
        savedQueries = memos.query ∧ final = memos ∧ next = inventory) ∧
      (∀ oldHandle, oldNode = some oldHandle →
        ∃ (old query : Node) (queried : Checked width),
          lookupNode beforeCaller.checked.native.machine.heap oldHandle = some old ∧
          next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [incoming, old] ∧
          SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old beforeCaller.checked query queried memos ∧
          (∀ ambient term,
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term) ∧
          (checkEmpty = false → replacement = query ∧
            afterCaller = SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge ∧
            final = memos)) := by
  obtain ⟨oldNode, oldScs, stored⟩ := pending
