structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width) (memos : Memos) : Prop where
  actual : Step left right before value after
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  extension : Extension before.native.machine after.native.machine
  available : Available after.native.machine.heap value
  closed : value.free = []
  meaning : ∀ ambient term,
    InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ↔
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term
  globals : Valid after.native.machine.heap memos
  events : ∃ events, SourceGlobalUnfold.Runs ⟨before.native.machine.heap, memos.unfolding⟩
    ⟨after.native.machine.heap, memos.unfolding⟩ events ∧ SourceGlobalUnfold.NoGlobal events

/-- Initial admission constructs the actual query, its next inventory, and every returned receipt. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (left right : Value Symbol Guard) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next : Inventory, ∃ value after,
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      Receipt formulas solver next left right before value after memos := by
