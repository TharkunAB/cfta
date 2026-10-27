/-- Retain the complete earlier capability and the prefix endpoint's counter and dependency levels.
The finish expression embeds the observation in the earlier proposition.
The recursive worker does not execute this finish expression. -/
def PrefixValid
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (result : Result width Typing) : Prop :=
  (match result with
    | .narrowed _ _ _ _ _ _ _ ordinary => ordinary = none
    | _ => True) ∧
  Valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    fuel fuel fuel fuel fuel fuel 0 0 0 0 0 uv caller before memos
    (finish checkEmpty edgesOf 0 0 0 0 0 uv result) ∧
  match result with
  | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
      after.core.counter = before.core.counter ∧
      ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
        EnumerationOrder.Stratified after.core level frontier
  | _ => True

/-- Original selected inputs derive one sufficient fuel for every prefix operation and every larger bound. -/
theorem prefix_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos) (safe : Safe before.core)
    (pending : EnumerationReferences.PendingReferences before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ fuel, ∀ extra,
      PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (fuel + extra) uv caller before memos
        (runPrefix holeKey fits admits graph templates stop order metadata
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          uv caller before memos.query) := by
