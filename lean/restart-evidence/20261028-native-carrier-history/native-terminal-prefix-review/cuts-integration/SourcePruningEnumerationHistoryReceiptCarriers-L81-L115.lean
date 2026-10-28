    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (references : ReferencesCarry before.core) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core ∧ FragmentCarries after.core fragment := by
  obtain ⟨entered, handle, scs, decoded, _edge, _headSeed, _inherited,
    _headInventory, _headCaller, _headMemos, _headBound,
    original, entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  have entrySuccess : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap workFuel uv)
      before.core (uv, handle, scs, decoded) entered.core := by
    rw [Success, entry]
    exact List.mem_singleton_self _
  have enteredFacts := SourcePruningEnumerationEntry.enter_carriers caller.checked.native.machine.heap
    workFuel uv before.core entered.core uv handle scs decoded original.safe.1.total references entrySuccess
  have completedFacts := completed.carriers enteredFacts.2.2
  exact ⟨completedFacts.1, enteredFacts.2.1.trans completedFacts.2.1, completedFacts.2.2⟩

/-- Either actual callback result retains the completed cache and fragment carriers. -/
theorem OrdinaryHistoryReceipt.carriers_after_callback
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (references : ReferencesCarry before.core)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) :
    UnionFind.Total callbackCore.representatives ∧ PreservesCarriers before.core callbackCore ∧
      ReferencesCarry callbackCore ∧ FragmentCarries callbackCore fragment := by
  have completedFacts := receipt.carriers references
  have recordedFacts := SourcePruningRecordTypes.recordTypes_carriers graph templates callbackFuel metadata uv
    (.inl fragment) after.core callbackCore result completedFacts.1 completedFacts.2.2.1 recorded
  exact ⟨recordedFacts.1, completedFacts.2.1.trans recordedFacts.2.1, recordedFacts.2.2,
    completedFacts.2.2.2.preserve fragment recordedFacts.2.1⟩

end MicroCFTA.SourcePruningEnumerationRecursive
