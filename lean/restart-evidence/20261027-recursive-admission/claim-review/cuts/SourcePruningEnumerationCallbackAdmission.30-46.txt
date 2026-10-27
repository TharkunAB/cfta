structure RecursiveCallbackAdmission
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (uv : Nat) (fragment : Fragments.Fragment Symbol) (recursiveFuel : Nat) (seed : Seed) (ceiling : Nat) : Prop where
  /-- The callback uses this actual native caller, full memo state and cache. -/
  packet : Packet formulas solver inventory caller memos metadata before
  /-- Every fragment hole names an allocated input variable. -/
  allocated : FragmentBound before.core.counter fragment
  /-- The actual native caller fits the planned callback profile. -/
  bounded : Fits seed.2 caller.checked
  /-- Every current native guard belongs to the planned callback carrier. -/
  known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap
  /-- The actual input cache fits the original mass ceiling. -/
  mass : suspendedBound before.core ≤ ceiling
  /-- The original reservation pays the smaller-depth recursive callback. -/
  reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling
