import MicroCFTA.SourcePruningEnumerationPreparedFuel
import MicroCFTA.SourcePruningEnumerationPrefixHistory

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
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
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Retain the complete earlier capability and the prefix endpoint's counter and dependency levels.
The finish expression embeds the observation in the earlier proposition. It is not an executed scan. -/
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
  obtain ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored, oldDecoded,
    _oldAvailable, _oldClosed, readExact, checkExact, checkReady, checkPaths, checkRealized,
    checkCounts, checkFlags, _checkIncoming, checkPending, parked, continued⟩ :=
    SourcePruningEnumerationSelectedOrdinary.complete_with_history formulas solver inventory caller memos
      holeKey fits admits metadata graph templates checkEmpty edgesOf before preference uv roots
      initial safe pending selection realized paths counts flags
  cases repeated with
  | true =>
      obtain ⟨_boundary, _cleared, _disabled, _waiting, resolved, countFuel, frame, _reading,
        _seen, written, indexed⟩ := parked rfl
      obtain ⟨counter, ordered⟩ := SourcePruningEnumerationParkedRestart.parked_order uv oldHandle scs
        before.core resolved checked.core stored frame written
      let bound := readFuel + checkFuel + countFuel
      refine ⟨bound, ?_⟩
      intro extra
      let w := bound + extra
      have readLe : readFuel ≤ w := by dsimp [w, bound]; omega
      have checkLe : checkFuel ≤ w := by dsimp [w, bound]; omega
      have countLe : countFuel ≤ w := by dsimp [w, bound]; omega
      have reading := readExact (w - readFuel)
      have checking := checkExact (w - checkFuel)
      rw [Nat.add_sub_of_le readLe] at reading
      rw [Nat.add_sub_of_le checkLe] at checking
      have index := indexed (w - countFuel)
      rw [Nat.add_sub_of_le countLe] at index
      have adapted := SourcePruningEnumerationParkedRestart.adapt_after_write caller.checked.native.machine.heap
        w uv oldHandle scs before checked resolved checked.core written index rfl
      have prefixRun : runPrefix holeKey fits admits graph templates stop order metadata w w w w w w
          uv caller before memos.query = .parked checked.core (some checked)
          (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata checked checked.core))) := by
        simp only [runPrefix, reading, checking, adapted, Option.map_some]
      refine ⟨prefix_no_ordinary holeKey fits admits graph templates stop order metadata
        w w w w w w uv caller before memos.query, ?_, ?_⟩
      · change Valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
          formulas solver inventory w w w w w w 0 0 0 0 0 uv caller before memos
          (run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            w w w w w w 0 0 0 0 0 uv caller before memos.query)
        rw [run_parked holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
          w w w w w w 0 0 0 0 0 uv oldHandle scs caller before checked memos.query
          readAfter checked.core reading checking adapted]
        exact ⟨oldHandle, scs, readAfter, reading, checking, checked, rfl, rfl,
          ⟨roots, checkPaths, checkReady.safe.1, checkRealized, checkCounts, checkFlags⟩,
          checkReady.safe, checkPending pending, counter, ordered, rfl⟩
      · rw [prefixRun]
        exact ⟨counter, ordered⟩
  | false =>
      obtain ⟨value, nativeFuel, heap, newHandle, final, narrowed, stable, post, _retained, query,
        _available, _closed, encoded, _decoded, rejected, completed⟩ := continued rfl
      by_cases empty : value = .empty
      · subst value
        let bound := readFuel + checkFuel + nativeFuel
        refine ⟨bound, ?_⟩
        intro extra
        let w := bound + extra
        have readLe : readFuel ≤ w := by dsimp [w, bound]; omega
        have checkLe : checkFuel ≤ w := by dsimp [w, bound]; omega
        have nativeLe : nativeFuel ≤ w := by dsimp [w, bound]; omega
        have reading := readExact (w - readFuel)
        have checking := checkExact (w - checkFuel)
        rw [Nat.add_sub_of_le readLe] at reading
        rw [Nat.add_sub_of_le checkLe] at checking
        obtain ⟨prepared, _noSuccess⟩ := rejected rfl w
        have preparedAt := SourcePruningEnumerationPreparedFuel.native_moreFuel holeKey fits admits metadata
          nativeFuel w uv oldHandle (w - nativeFuel) scs oldValue .empty caller.checked.native.machine.heap
          heap (some reject) narrowed stable prepared
        rw [Nat.add_sub_of_le nativeLe] at preparedAt
        have narrowedAt := stable (w - nativeFuel)
        rw [Nat.add_sub_of_le nativeLe] at narrowedAt
        have prefixRun : runPrefix holeKey fits admits graph templates stop order metadata w w w w w w
            uv caller before memos.query =
            .narrowed checked.core (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
              memos.query (some []) none none none := by
          simp only [runPrefix, reading, checking, oldDecoded, preparedAt]
          rfl
        refine ⟨prefix_no_ordinary holeKey fits admits graph templates stop order metadata
          w w w w w w uv caller before memos.query, ?_, ?_⟩
        · change Valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            formulas solver inventory w w w w w w 0 0 0 0 0 uv caller before memos
            (run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
              w w w w w w 0 0 0 0 0 uv caller before memos.query)
          rw [run_empty holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            w w w w w w 0 0 0 0 0 uv oldHandle scs oldValue caller before memos.query
            readAfter checked.core heap reading checking oldDecoded preparedAt]
          exact ⟨oldHandle, scs, readAfter, reading, checking, oldValue, .empty, heap, reject,
            final, oldDecoded, narrowedAt, preparedAt, rfl, rfl, rfl, post, query,
            Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        · rw [prefixRun]
          trivial
      · obtain ⟨representativeFuel, countFuel, action, after, prepared, observed, shape, waiting, afterReady,
          afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, _afterIncoming,
          _callback, ordinary⟩ := completed empty
        obtain ⟨indexFuel, adapted⟩ := SourcePruningEnumerationNarrowAdapter.complete heap uv oldHandle newHandle
          representativeFuel countFuel scs before after checked.core shape
        have readSuccess : Success (getValue readFuel uv) before.core
            (.unenumerated (some oldHandle) scs) readAfter := by
          rw [Success, ← Nat.add_zero readFuel, readExact 0]
          exact List.mem_singleton_self _
        have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
            caller.checked.native.machine.heap checkFuel uv oldHandle scs) readAfter false checked.core := by
          rw [Success, ← Nat.add_zero checkFuel, checkExact 0]
          exact List.mem_singleton_self _
        have history := SourcePruningEnumerationPrefixHistory.complete caller.checked.native.machine.heap
          before after readAfter checked.core readFuel checkFuel representativeFuel uv oldHandle newHandle scs
          safe stored readSuccess checkSuccess (by
            rcases shape with ⟨_same, equal⟩ | ⟨_different, resolved, reading, written, _indexed⟩
            · exact Or.inl equal
            · exact Or.inr ⟨resolved, reading, written⟩)
        let bound := readFuel + checkFuel + nativeFuel + representativeFuel + indexFuel
        refine ⟨bound, ?_⟩
        intro extra
        let w := bound + extra
        have readLe : readFuel ≤ w := by dsimp [w, bound]; omega
        have checkLe : checkFuel ≤ w := by dsimp [w, bound]; omega
        have nativeLe : nativeFuel ≤ w := by dsimp [w, bound]; omega
        have representativeLe : representativeFuel ≤ w := by dsimp [w, bound]; omega
        have indexLe : indexFuel ≤ w := by dsimp [w, bound]; omega
        have reading := readExact (w - readFuel)
        have checking := checkExact (w - checkFuel)
        rw [Nat.add_sub_of_le readLe] at reading
        rw [Nat.add_sub_of_le checkLe] at checking
        have adaptedAt := adapted (w - indexFuel)
        rw [Nat.add_sub_of_le indexLe] at adaptedAt
        obtain ⟨nextAction, preparedAt, raw⟩ := SourcePruningEnumerationPreparedFuel.nonempty_moreFuel
          holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value
          caller.checked.native.machine.heap heap action checked.core after.core narrowed stable empty encoded prepared
          observed (w - nativeFuel) (w - representativeFuel)
        rw [Nat.add_sub_of_le nativeLe, Nat.add_sub_of_le representativeLe] at preparedAt
        have narrowedAt := stable (w - nativeFuel)
        rw [Nat.add_sub_of_le nativeLe] at narrowedAt
        have right : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates w metadata uv
            (.inr newHandle) after.core) = [.ok ((false, metadata), after.core)] := by
          rw [SourcePruningRecordTypes.recordTypes_inr]
          rfl
        have prefixRun : runPrefix holeKey fits admits graph templates stop order metadata w w w w w w
            uv caller before memos.query = .narrowed checked.core (.done (value, some nextAction) heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
              memos.query (some [.ok ((), after.core)]) (some after)
              (some [.ok ((false, metadata), after.core)]) none := by
          simp only [runPrefix, reading, checking, oldDecoded, preparedAt, raw, encoded, adaptedAt, right]
          rfl
        refine ⟨prefix_no_ordinary holeKey fits admits graph templates stop order metadata
          w w w w w w uv caller before memos.query, ?_, ?_⟩
        · change Valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            formulas solver inventory w w w w w w 0 0 0 0 0 uv caller before memos
            (run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
              w w w w w w 0 0 0 0 0 uv caller before memos.query)
          rw [run_narrowed holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            w w w w w w 0 0 0 0 0 uv oldHandle newHandle scs oldValue value caller before after memos.query
            readAfter checked.core heap nextAction reading checking oldDecoded preparedAt raw encoded adaptedAt]
          refine ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap, nextAction,
            final, oldDecoded, narrowedAt, preparedAt, rfl, rfl, rfl, post, query, Or.inr
              ⟨newHandle, after, empty, encoded, rfl, rfl,
                ⟨roots, afterPaths, afterReady.safe.1, afterRealized, afterCounts, afterFlags⟩,
                afterReady.safe, afterPending pending, afterReady, afterStored, waiting, rfl, rfl, ?_⟩⟩
          intro parentEntry storedEdges depth free parent nonterminal selected ranges
          obtain ⟨R, N, P, H, K, entered, processed, lastCaller, saved, last, next, outcome,
            ordinaryRun, _render, _sameFlags, _sameWaiting, lastPost, lastQuery, admitted,
            receiptHistory, receiptPosts, fragments, callbacks, outcomeShape, supported⟩ :=
            ordinary parentEntry storedEdges depth free parent nonterminal selected (by simpa only [query] using ranges)
          refine ⟨R, N, P, H, K, entered, processed, lastCaller, saved, last, next, outcome,
            ?_, lastPost, lastQuery, admitted, receiptHistory, receiptPosts, fragments, callbacks, outcomeShape, supported⟩
          intro er en ep eh ek
          rw [run_narrowed holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            w w w w w w (R + er) (N + en) (P + ep) (H + eh) (K + ek)
            uv oldHandle newHandle scs oldValue value caller before after memos.query readAfter checked.core heap
            nextAction reading checking oldDecoded preparedAt raw encoded adaptedAt]
          have actual := ordinaryRun er en (P + ep) (H + eh) ek (Nat.le_add_right _ _) (Nat.le_add_right _ _)
          rw [show SourcePruningEnumerationNativeOrdinary.run checkEmpty (R + er) (N + en) (P + ep) (H + eh)
            (K + ek) uv edgesOf
            (SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
            after memos.query = _ from (by simpa only [query] using actual)]
        · rw [prefixRun]
          exact history

end MicroCFTA.SourcePruningEnumerationSelectedStep
