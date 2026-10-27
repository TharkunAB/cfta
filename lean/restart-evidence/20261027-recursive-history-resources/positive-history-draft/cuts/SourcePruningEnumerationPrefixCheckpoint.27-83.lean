/-- Original selected inputs give one common bound and a fixed resume phase.
Only the accepted branch's prepared action may change with fuel.
Every observation retains the full earlier prefix capability.
This result does not assert completion of the recursive continuation. -/
theorem prefix_checkpoint_complete
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
    ∃ fuel,
      (∃ checked : Cached, ∀ extra,
        runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query =
          .parked checked.core (some checked)
            (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata checked checked.core))) ∧
        PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            formulas solver inventory (fuel + extra) uv caller before memos
            (runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query)) ∨
      (∃ (checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint), ∀ extra,
        runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query =
          .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
            (SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
            memos.query (some []) none none none ∧
        PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            formulas solver inventory (fuel + extra) uv caller before memos
            (runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query)) ∨
      (∃ (checked : Core) (value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
          (after : Cached), value ≠ .empty ∧ ∀ extra, ∃ action : EnumerateM Symbol Constraint Unit,
        runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query =
          .narrowed checked (.done (value, some action) heap)
            (SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
            memos.query (some [.ok ((), after.core)]) (some after)
            (some [.ok ((false, metadata), after.core)]) none ∧
        PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            formulas solver inventory (fuel + extra) uv caller before memos
            (runPrefix holeKey fits admits graph templates stop order metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query)) := by
