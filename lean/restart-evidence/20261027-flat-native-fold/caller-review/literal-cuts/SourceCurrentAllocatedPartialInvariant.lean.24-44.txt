/-- Every entry retains initial physical facts and all phase-appropriate warm laws. -/
structure Context (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (state : Caller width) (memos : Memos) : Prop where
  ready : SourceCurrentConjunctionClassScan.Ready state.checked
  admitted : At formulas solver inventory state.checked
  sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver state
  stored : SourceCurrentMemoMergeEffects.Stored state.checked.native.machine.heap state.merge
  covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient state.merge
  correct : SourceCurrentEmptinessMemo.Correct formulas solver state.checked.native.machine.heap state.fourth
  globals : EndpointMemoGateTrace.Valid state.checked.native.machine.heap memos
  probes : InternedFreshOrdinaryProbeHeap.Heap state.checked.native.machine.heap

/-- A returned caller retains its actual current context and completed table history. -/
structure Post (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (next : Inventory)
    (before after : Caller width) (final : Memos) : Prop where
  context : Context formulas solver next after final
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked)
  retained : Cache.Extends before.merge after.merge
  fourthRetained : SourceCurrentEmptinessMemo.Extends before.fourth after.fourth
