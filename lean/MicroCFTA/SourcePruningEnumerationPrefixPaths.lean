import MicroCFTA.SourcePruningEnumerationPrefixCompletion
import MicroCFTA.SourcePruningEnumerationPathStorage

/-!
# Original bucket paths at actual selected prefix caches

Actual frames and same-bucket writes supply the path predicate.
A common sum bound retains every existing PrefixValid clause.
-/
namespace MicroCFTA.SourcePruningEnumerationPrefixHistory
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type} {P : EqualityTrie.Path → Prop}

private theorem after_action_paths
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (readAfter checked : EnumerationState.State Symbol EnumGuard)
    (readFuel checkFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (safe : EnumerationSchedule.Safe before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some oldHandle) scs))
    (read : Success (getValue readFuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter)
    (check : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv oldHandle scs)
      readAfter false checked)
    (shape : after = EnumerationExpandableIndex.frame checked before ∨
      ∃ resolved : EnumerationState.State Symbol EnumGuard,
        Success (representative representativeFuel uv) checked uv resolved ∧
        Success (setValue uv (.unenumerated (some newHandle) scs)) resolved () after.core)
    (originalPaths : StatePaths P before.core) : StatePaths P after.core := by
  have readFrame := (getValue_frame readFuel uv before.core readAfter _ safe.1.total read).1
  have checkedFrame := readFrame.trans
    (SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame heap checkFuel uv oldHandle scs
      readAfter checked (readFrame.total safe.1.total) check)
  have checkedPaths := SourcePruningEnumerationPathStorage.values_paths originalPaths checkedFrame.values
  rcases shape with equal | ⟨resolved, reading, written⟩
  · simpa only [equal, EnumerationExpandableIndex.frame] using checkedPaths
  · have resolvedPaths := SourcePruningEnumerationPathStorage.representative_paths
      representativeFuel uv uv checked resolved checkedPaths reading
    have inherited : BucketPaths P scs := originalPaths _ (List.mem_of_getElem? stored)
    exact SourcePruningEnumerationPathStorage.setValue_paths uv (.unenumerated (some newHandle) scs)
      resolved after.core resolvedPaths inherited written

end MicroCFTA.SourcePruningEnumerationPrefixHistory

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
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

section PathBound
variable [DecidableEq (EdgeKey Symbol Constraint)]

include checkEmpty edgesOf in
private theorem prefix_paths_complete
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
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (P : EqualityTrie.Path → Prop)
    (originalPaths : SourcePruningEnumerationPathTransport.StatePaths P before.core) :
    ∃ fuel, ∀ extra,
      match runPrefix holeKey fits admits graph templates stop order metadata
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          uv caller before memos.query with
      | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
          SourcePruningEnumerationPathTransport.StatePaths P after.core
      | _ => True := by
  classical
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
      have resolvedStoredPaths := SourcePruningEnumerationPathStorage.values_paths originalPaths frame.values
      have checkedStoredPaths := SourcePruningEnumerationPathStorage.setValue_paths uv
        (.unenumerated (some oldHandle) []) resolved checked.core resolvedStoredPaths
        (by intro sc impossible; cases impossible) written
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
      rw [prefixRun]
      exact checkedStoredPaths
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
        rw [prefixRun]
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
        have storedPaths := SourcePruningEnumerationPrefixHistory.after_action_paths caller.checked.native.machine.heap
          before after readAfter checked.core readFuel checkFuel representativeFuel uv oldHandle newHandle scs
          safe stored readSuccess checkSuccess (by
            rcases shape with ⟨_same, equal⟩ | ⟨_different, resolved, reading, written, _indexed⟩
            · exact Or.inl equal
            · exact Or.inr ⟨resolved, reading, written⟩) originalPaths
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
        rw [prefixRun]
        exact storedPaths

end PathBound

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual common prefix bound retains validity and the original stored paths. -/
theorem prefix_complete_with_paths
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
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (P : EqualityTrie.Path → Prop)
    (originalPaths : SourcePruningEnumerationPathTransport.StatePaths P before.core) :
    ∃ fuel, ∀ extra,
      let observed := runPrefix holeKey fits admits graph templates stop order metadata
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          uv caller before memos.query
      PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (fuel + extra) uv caller before memos observed ∧
      match observed with
      | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
          SourcePruningEnumerationPathTransport.StatePaths P after.core
      | _ => True := by
  obtain ⟨validBound, valid⟩ := prefix_complete holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory caller memos before preference uv roots initial safe pending selection realized
    paths counts flags
  obtain ⟨pathBound, preserved⟩ := prefix_paths_complete holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory caller memos before preference uv roots initial safe pending selection realized
    paths counts flags P originalPaths
  refine ⟨validBound + pathBound, ?_⟩
  intro extra
  dsimp only
  constructor
  · simpa only [Nat.add_assoc] using valid (pathBound + extra)
  · have actual := preserved (validBound + extra)
    have same : pathBound + (validBound + extra) = validBound + pathBound + extra := by omega
    rw [same] at actual
    exact actual

end MicroCFTA.SourcePruningEnumerationSelectedStep
