import MicroCFTA.SourcePruningEnumerationSelectedOrdinary
import MicroCFTA.SourcePruningEnumerationSelectedStep

/-! Empty original target history yields the actual non-repeated selected prefix. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentSelectedNoHistoryCheck
open Cache EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The empty-history condition concerns the original selected cache only. -/
theorem selected_without_target_history
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (before : Cached) (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos) (safe : Safe before.core)
    (pending : EnumerationReferences.PendingReferences before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (noHistory : before.core.recursionAncestry uv = []) :
    ∃ (readFuel oldHandle : Nat) (scs : List Suspended) (oldValue : Node)
      (readAfter : Core) (checkFuel : Nat) (checked : Cached)
      (nativeFuel representativeFuel : Nat) (result : Node)
      (heap : InternedConstructorTemplates.State Symbol Constraint) (final : Memos)
      (action : EnumerateM Symbol Constraint Unit),
      before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) ∧
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]) ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap (checkFuel + extra) uv oldHandle scs readAfter) =
        [.ok (false, checked.core)]) ∧
      SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue
        caller.checked.native.machine.heap = .done result heap ∧
      Post formulas solver inventory caller
        (SourceCurrentAllocatedPartialState.advance caller
          (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge) final ∧
      final.query = memos.query ∧
      SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
        uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (result, some action) heap ∧
      (match oldValue with
       | .mu .. => result = oldValue ∧ heap = caller.checked.native.machine.heap
       | _ => True) ∧
      (∀ er ec indexFuel callbackFuel,
        match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          (readFuel + er) (checkFuel + ec) nativeFuel representativeFuel indexFuel callbackFuel
          uv caller before memos.query with
        | .narrowed actualChecked prepared reached queries _ _ _ ordinary =>
            actualChecked = checked.core ∧ prepared = .done (result, some action) heap ∧
            reached = SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge ∧
            queries = memos.query ∧ ordinary = none
        | _ => False) := by
  letI : DecidableEq Symbol := by
    classical
    exact inferInstance
  letI : DecidableEq Node := by
    classical
    exact inferInstance
  obtain ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored,
    decoded, _available, _closed, readExact, checkExact, _ready, _paths, _realized,
    _counts, _checkedFlags, _avoid, _pending, parked, continued⟩ :=
    SourcePruningEnumerationSelectedOrdinary.complete_with_history formulas solver inventory caller memos
      holeKey fits admits metadata graph templates checkEmpty edgesOf before preference uv roots
      initial safe pending selection realized paths counts flags
  have repeatedFalse : repeated = false := by
    cases repeated with
    | false => rfl
    | true =>
        obtain ⟨_boundary, _cleared, _disabled, _waiting, resolved, _countFuel, frame, _reading,
          seen, _written, _indexed⟩ := parked rfl
        rw [frame.recursionAncestry, noHistory] at seen
        simp at seen
  have checkFalse (extra : Nat) :
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        (checkFuel + extra) uv oldHandle scs readAfter) = [.ok (false, checked.core)] := by
    simpa only [repeatedFalse] using checkExact extra
  obtain ⟨result, nativeFuel, heap, _newHandle, final, narrowed, _stable, post, _extends, query,
    _resultAvailable, _resultClosed, _encoded, _decodedAfter, rejected, completed⟩ := continued repeatedFalse
  have preparedExists : ∃ (representativeFuel : Nat) (action : EnumerateM Symbol Constraint Unit),
      SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
        uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (result, some action) heap := by
    by_cases empty : result = .empty
    · exact ⟨0, reject, (rejected empty 0).1⟩
    · obtain ⟨representativeFuel, _countFuel, action, _after, prepared, _rest⟩ := completed empty
      exact ⟨representativeFuel, action, prepared⟩
  obtain ⟨representativeFuel, action, prepared⟩ := preparedExists
  refine ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, checked, nativeFuel,
    representativeFuel, result, heap, final, action, stored, decoded, readExact, checkFalse,
    narrowed, post, query, prepared, ?_, ?_⟩
  · cases oldValue <;> try trivial
    simp only [SourcePruningOuterNarrow.narrow] at narrowed
    cases narrowed
    exact ⟨rfl, rfl⟩
  · intro er ec indexFuel callbackFuel
    have observed : ∃ (raw : Option (List (Except Error (Unit × Core))))
        (candidate : Option Cached)
        (right : Option (List (Except Error ((Bool × SourcePruningRecordTypes.Metadata Typing) × Core)))),
        SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          (readFuel + er) (checkFuel + ec) nativeFuel representativeFuel indexFuel callbackFuel
          uv caller before memos.query =
        .narrowed checked.core (.done (result, some action) heap)
          (SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
          memos.query raw candidate right none := by
      simp only [SourcePruningEnumerationSelectedStep.runPrefix,
        SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, readExact er, checkFalse ec, decoded,
        ← SourcePruningEnumerationAction.prepare_configured_eq, prepared]
      repeat' first
        | exact ⟨_, _, _, rfl⟩
        | split
    obtain ⟨raw, candidate, right, observed⟩ := observed
    rw [observed]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end MicroCFTA.SourceCurrentSelectedNoHistoryCheck
