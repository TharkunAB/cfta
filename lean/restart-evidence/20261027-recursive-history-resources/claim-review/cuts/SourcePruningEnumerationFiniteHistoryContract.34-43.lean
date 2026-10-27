def HistoryAdmission
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (recursiveFuel : Nat) (seed : Seed) (ceiling : Nat) : Prop :=
  Packet formulas solver inventory caller memos metadata before ∧
  Fits seed.2 caller.checked ∧
  Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
  suspendedBound before.core ≤ ceiling ∧
  SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling
