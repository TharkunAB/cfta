structure Packet (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (before : Cached) : Prop where
  /-- The native caller satisfies the context at the full memo state. -/
  context : Context formulas solver inventory caller memos
  /-- The enumeration core has safe storage and live roots. -/
  safe : EnumerationSchedule.Safe before.core
  /-- Suspended references avoid every enumerated class. -/
  pending : EnumerationReferences.PendingReferences before.core
  /-- The captured cache retains native handles and both indexes. -/
  valid : CacheValid caller before
  /-- Stored fragments admit dependency levels below a finite frontier. -/
  ordered : ∃ level frontier, EnumerationOrder.Stratified before.core level frontier
  /-- Every pending template entry names an allocated variable. -/
  bounded : ∀ group ∈ metadata.pending, SourcePruningPartialMatch.PendingBound before.core.counter group
