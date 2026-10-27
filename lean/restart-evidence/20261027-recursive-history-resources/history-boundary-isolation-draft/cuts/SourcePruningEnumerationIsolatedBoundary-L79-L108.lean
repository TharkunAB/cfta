
/-- The actual restart gate at the original packet cannot select the isolated boundary. -/
theorem packet_restart_ne
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (held handle uv : Nat) (value : Value Symbol Constraint)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (isolated : IsolatedPending held handle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    uv ≠ held := by
  have selected : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨_roots, _paths, _storage, _realized, _counts, flags⟩ := packet.valid
  exact isolated.selected_ne caller.checked.native.machine.heap before held handle value (order metadata) uv
    decoded boundary flags selected

end Packet
end MicroCFTA.EnumerationDischargeHistory
