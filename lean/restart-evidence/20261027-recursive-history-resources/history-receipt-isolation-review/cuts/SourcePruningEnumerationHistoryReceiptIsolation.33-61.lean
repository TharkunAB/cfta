/-- The exact entry and head receipts retain a different original isolated slot. -/
theorem OrdinaryHistoryReceipt.isolated
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (isolated : IsolatedPending held heldHandle before.core) (different : held ≠ uv) :
    IsolatedPending held heldHandle after.core := by
  obtain ⟨entered, handle, scs, decoded, edge, headSeed, inherited,
    headInventory, headCaller, headMemos, headBound,
    original, entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  have enteredIsolated := isolated.through_entry_row caller.checked.native.machine.heap workFuel uv
    before.core entered.core held heldHandle uv handle scs decoded original.safe.1.total entry
  exact completed.isolated enteredIsolated different

/-- Either actual callback result retains the slot after the same completed history receipt. -/
theorem OrdinaryHistoryReceipt.isolated_after_callback
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (callbackCore : Core)
    (isolated : IsolatedPending held heldHandle before.core) (different : held ≠ uv)
    (recorded : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) after.core result callbackCore) :
    IsolatedPending held heldHandle callbackCore := by
  have capturedIsolated := receipt.isolated isolated different
  obtain ⟨entered, handle, scs, decoded, edge, headSeed, inherited,
    headInventory, headCaller, headMemos, headBound,
    _original, _entry, _enteredPacket, _post, _captured, completed⟩ := receipt
  exact capturedIsolated.through_recordTypes graph templates callbackFuel metadata uv (.inl fragment)
    after.core callbackCore result completed.completed.safe.1.total recorded
