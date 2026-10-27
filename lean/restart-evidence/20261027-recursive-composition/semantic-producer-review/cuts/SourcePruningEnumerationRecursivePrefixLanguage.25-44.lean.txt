theorem packet_selected_ready
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : Caller width) (memos : Memos) (before : Cached) (uv : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    EnumerationDriver.Ready uv before.core := by
  have selection : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨roots, paths, _storage, _realized, counts, flags⟩ := packet.valid
  exact SourcePruningEnumerationSelection.ready caller.checked.native.machine.heap before
    (order metadata) uv packet.safe roots paths counts flags selection
