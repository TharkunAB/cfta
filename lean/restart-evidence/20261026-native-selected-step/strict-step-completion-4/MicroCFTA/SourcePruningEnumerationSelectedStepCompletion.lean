import MicroCFTA.SourcePruningEnumerationSelectedStep
import MicroCFTA.SourcePruningEnumerationSelectedOrdinary

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
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)

attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- The actual nonempty preparation fixes its pure or representative-and-write action. -/
theorem prepared_action
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle) :
    SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap =
      .done (value, some (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs))) nextHeap := by
  cases value with
  | empty => exact False.elim (nonempty rfl)
  | reference name => simp [encodeNode] at encoded
  | node entry edges depth free => simp only [SourcePruningEnumerationAction.prepare, narrowed, encoded]
  | union entry members depth free => simp only [SourcePruningEnumerationAction.prepare, narrowed, encoded]
  | mu entry body depth ordinary => simp only [SourcePruningEnumerationAction.prepare, narrowed, encoded]

/-- Successful preparation has one raw row at its actual reached core. -/
theorem prepared_singleton
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (checked after : Core)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) :
    ExceptT.run (action checked) = [.ok ((), after)] := by
  have actual := prepared_action holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle newHandle
    scs oldValue value heap nextHeap narrowed nonempty encoded
  rw [prepared] at actual
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actual).1).2
  rw [actionSame] at observed ⊢
  by_cases same : newHandle = oldHandle
  · rw [ite_eq_left same] at observed ⊢
    obtain ⟨_unit, rfl⟩ := (success_pure () () checked after).mp observed
    rfl
  · rw [ite_eq_right same] at observed ⊢
    obtain ⟨selected, resolved, reading, writing⟩ := (success_bind _ _ checked () after).mp observed
    obtain ⟨found, lookup, selectedSame, resolvedSame⟩ :=
      (representative_success representativeFuel uv checked resolved selected).mp reading
    have raw : representative representativeFuel uv checked = [.ok (selected, resolved)] := by
      rw [selectedSame, resolvedSame]
      exact representative_exact representativeFuel uv checked found lookup
    rw [bind_single _ _ checked resolved selected raw]
    have afterSame := (EnumerationDriver.modify_success _ resolved after).mp writing
    rw [afterSame]
    rfl

variable [DecidableEq Symbol] [DecidableEq Node]

/-- The actual repeated check executes only the indexed parked restart. -/
theorem run_parked
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv oldHandle : Nat)
    (scs : List Suspended) (caller : Caller width) (before parked : Cached) (queries : Queries)
    (readAfter checked : Core)
    (read : ExceptT.run (getValue readFuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (check : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      checkFuel uv oldHandle scs readAfter) = [.ok (true, checked)])
    (adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
      indexFuel uv oldHandle scs before checked = some parked) :
    run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv caller before queries =
      .parked checked (some parked)
        (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked))) := by
  simp only [run, read, check, adapted, Option.map_some]

/-- Empty narrowing retains the reached caller and rejects before later callbacks. -/
theorem run_empty
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv oldHandle : Nat)
    (scs : List Suspended) (oldValue : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (readAfter checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (read : ExceptT.run (getValue readFuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (check : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue caller.checked.native.machine.heap =
      .done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap) :
    run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv caller before queries =
      .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
        (SourceCurrentAllocatedPartialState.advance caller
          (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
        queries (some []) none none none := by
  simp only [run, read, check, decoded, prepared]
  rfl

/-- A successful actual action and attached cache reach the concrete Right callback and ordinary worker. -/
theorem run_narrowed
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv oldHandle newHandle : Nat)
    (scs : List Suspended) (oldValue value : Node) (caller : Caller width) (before after : Cached)
    (queries : Queries) (readAfter checked : Core)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (action : EnumerateM Symbol Constraint Unit)
    (read : ExceptT.run (getValue readFuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (check : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (value, some action) heap)
    (raw : ExceptT.run (action checked) = [.ok ((), after.core)])
    (encoded : encodeNode value = some newHandle)
    (adapted : SourcePruningEnumerationNarrowAdapter.adapt heap indexFuel uv oldHandle newHandle scs
      before after.core = some after) :
    run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv caller before queries =
      .narrowed checked (.done (value, some action) heap)
        (SourceCurrentAllocatedPartialState.advance caller
          (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
        queries (some [.ok ((), after.core)]) (some after)
        (some [.ok ((false, metadata), after.core)])
        (some (SourcePruningEnumerationNativeOrdinary.run checkEmpty r n p h k uv edgesOf
          (SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
          after queries)) := by
  have right : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inr newHandle) after.core) = [.ok ((false, metadata), after.core)] := by
    rw [SourcePruningRecordTypes.recordTypes_inr]
    rfl
  simp only [run, read, check, decoded, prepared, raw, encoded, adapted, right]
  rfl

/-- Admit only reached parked or nonempty caches; retain Empty rejection and bounded ordinary observations. -/
def Valid
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv : Nat)
    (caller : Caller width) (before : Cached) (memos : Memos) : Result width Typing → Prop := fun result =>
  ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
    ExceptT.run (getValue readFuel uv before.core) = [.ok (.unenumerated (some oldHandle) scs, readAfter)] ∧
    match result with
    | .stopped _ _ => False
    | .parked checked candidate raw =>
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          checkFuel uv oldHandle scs readAfter) = [.ok (true, checked)] ∧
        ∃ after : Cached, candidate = some after ∧ after.core = checked ∧
          SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after ∧ Safe after.core ∧
          EnumerationReferences.PendingReferences after.core ∧ after.core.counter = before.core.counter ∧
          (∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
            EnumerationOrder.Stratified after.core level frontier) ∧
          raw = some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata after checked))
    | .narrowed checked prepared reached queries action candidate right ordinary =>
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)] ∧
        ∃ (oldValue value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
          (selectedAction : EnumerateM Symbol Constraint Unit) (final : Memos),
          lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
          SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue
            caller.checked.native.machine.heap = .done value heap ∧
          SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
            uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (value, some selectedAction) heap ∧
          prepared = .done (value, some selectedAction) heap ∧
          reached = SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge ∧
          queries = memos.query ∧ Post formulas solver inventory caller reached final ∧ final.query = queries ∧
          ((value = .empty ∧ action = some [] ∧ candidate = none ∧ right = none ∧ ordinary = none) ∨
            ∃ (newHandle : Nat) (after : Cached), value ≠ .empty ∧ encodeNode value = some newHandle ∧
              action = some [.ok ((), after.core)] ∧ candidate = some after ∧
              SourcePruningEnumerationNativeBranchCompletion.CacheValid reached after ∧ Safe after.core ∧
              EnumerationReferences.PendingReferences after.core ∧ EnumerationDriver.Ready uv after.core ∧
              after.core.values[uv]? = some (.unenumerated (some newHandle) scs) ∧
              after.waiting = before.waiting ∧
              right = some [.ok ((false, metadata), after.core)] ∧
              ordinary = some (SourcePruningEnumerationNativeOrdinary.run
                checkEmpty r n p h k uv edgesOf reached after queries) ∧
              ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
                (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
                (free : List InternedBinderProtocol.Reference),
                value = .node parentEntry storedEdges depth free →
                scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false →
                (∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), edge ∈ storedEdges) →
                SourcePruningEnumerationNativeOrdinary.Ranges checkEmpty uv edgesOf reached after queries →
                ∃ (R N P H K : Nat) (entered : Cached)
                  (processed : List (SourcePruningEnumerationSelectedEdge.Result width))
                  (lastCaller : Caller width) (saved : Queries) (last : Memos) (next : Inventory)
                  (outcome : SourcePruningEnumerationNativeBranches.Result width),
                  (∀ er en ep eh ek,
                    run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
                      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel
                      (R + er) (N + en) (P + ep) (H + eh) (K + ek) uv caller before memos.query =
                      .narrowed checked prepared reached queries action candidate right
                        (some ([.ok ((uv, newHandle, scs, .node parentEntry storedEdges depth free), entered.core)],
                          some outcome))) ∧
                  Post formulas solver next caller lastCaller last ∧ last.query = saved ∧
                  (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Admitted uv receipt) ∧
                  (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.FragmentHistory before.core receipt) ∧
                  (∀ receipt ∈ processed,
                    SourcePruningEnumerationReceiptCallback.Completes graph templates metadata uv before.core receipt) ∧
                  (outcome = .complete processed lastCaller saved ∨ outcome = .stopped processed (some .unhandled)) ∧
                  ((∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), arityAllows edge.children.length scs = true →
                    SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
                    outcome = .complete processed lastCaller saved))

/-- Genuine selection reaches one parked restart or the same narrowing and concrete continuation observations. -/
theorem complete
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
    ∃ readFuel checkFuel nativeFuel representativeFuel indexFuel,
      ∀ er ec ei callbackFuel r n p h k,
        Valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
          (readFuel + er) (checkFuel + ec) nativeFuel representativeFuel (indexFuel + ei) callbackFuel
          r n p h k uv caller before memos
          (run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            (readFuel + er) (checkFuel + ec) nativeFuel representativeFuel (indexFuel + ei)
            callbackFuel r n p h k uv caller before memos.query) := by
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
      refine ⟨readFuel, checkFuel, 0, 0, countFuel, ?_⟩
      intro er ec ei callbackFuel r n p h k
      have adapted := SourcePruningEnumerationParkedRestart.adapt_after_write caller.checked.native.machine.heap
        (countFuel + ei) uv oldHandle scs before checked resolved checked.core written (indexed ei) rfl
      rw [run_parked holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        (readFuel + er) (checkFuel + ec) 0 0 (countFuel + ei) callbackFuel r n p h k uv oldHandle
        scs caller before checked memos.query readAfter checked.core (readExact er) (checkExact ec) adapted]
      exact ⟨oldHandle, scs, readAfter, readExact er, checkExact ec, checked, rfl, rfl,
        ⟨roots, checkPaths, checkReady.safe.1, checkRealized, checkCounts, checkFlags⟩,
        checkReady.safe, checkPending pending, counter, ordered, rfl⟩
  | false =>
      obtain ⟨value, nativeFuel, heap, newHandle, final, narrowed, _stable, post, _retained, query,
        _available, _closed, encoded, _decoded, rejected, completed⟩ := continued rfl
      by_cases empty : value = .empty
      · subst value
        obtain ⟨prepared, _noSuccess⟩ := rejected rfl 0
        refine ⟨readFuel, checkFuel, nativeFuel, 0, 0, ?_⟩
        intro er ec ei callbackFuel r n p h k
        rw [run_empty holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
          (readFuel + er) (checkFuel + ec) nativeFuel 0 (0 + ei) callbackFuel r n p h k uv oldHandle
          scs oldValue caller before memos.query readAfter checked.core heap
          (readExact er) (checkExact ec) oldDecoded prepared]
        exact ⟨oldHandle, scs, readAfter, readExact er, checkExact ec, oldValue, .empty, heap, reject,
          final, oldDecoded, narrowed, prepared, rfl, rfl, rfl, post, query,
          Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      · obtain ⟨representativeFuel, countFuel, action, after, prepared, observed, shape, waiting, afterReady,
          afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, _afterIncoming,
          _callback, ordinary⟩ := completed empty
        have raw := prepared_singleton holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
          newHandle scs oldValue value caller.checked.native.machine.heap heap action checked.core after.core
          narrowed empty encoded prepared observed
        obtain ⟨indexFuel, adapted⟩ := SourcePruningEnumerationNarrowAdapter.complete heap uv oldHandle newHandle
          representativeFuel countFuel scs before after checked.core shape
        refine ⟨readFuel, checkFuel, nativeFuel, representativeFuel, indexFuel, ?_⟩
        intro er ec ei callbackFuel r n p h k
        rw [run_narrowed holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
          (readFuel + er) (checkFuel + ec) nativeFuel representativeFuel (indexFuel + ei) callbackFuel
          r n p h k uv oldHandle newHandle scs oldValue value caller before after memos.query readAfter
          checked.core heap action (readExact er) (checkExact ec) oldDecoded prepared raw encoded (adapted ei)]
        refine ⟨oldHandle, scs, readAfter, readExact er, checkExact ec, oldValue, value, heap, action,
          final, oldDecoded, narrowed, prepared, rfl, rfl, rfl, post, query, Or.inr
            ⟨newHandle, after, empty, encoded, rfl, rfl,
              ⟨roots, afterPaths, afterReady.safe.1, afterRealized, afterCounts, afterFlags⟩,
              afterReady.safe, afterPending pending, afterReady, afterStored, waiting, rfl, rfl, ?_⟩⟩
        intro parentEntry storedEdges depth free parent nonterminal selected ranges
        obtain ⟨R, N, P, H, K, entered, processed, lastCaller, saved, last, next, outcome,
          ordinaryRun, _render, _sameFlags, _sameWaiting, lastPost, lastQuery, admitted,
          _history, _receiptPosts, fragments, callbacks, outcomeShape, supported⟩ :=
          ordinary parentEntry storedEdges depth free parent nonterminal selected (by simpa only [query] using ranges)
        refine ⟨R, N, P, H, K, entered, processed, lastCaller, saved, last, next, outcome,
          ?_, lastPost, lastQuery, admitted, fragments, callbacks, outcomeShape, supported⟩
        intro ordinaryReadExtra ordinaryNativeExtra ep eh ek
        rw [run_narrowed holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
          (readFuel + er) (checkFuel + ec) nativeFuel representativeFuel (indexFuel + ei) callbackFuel
          (R + ordinaryReadExtra) (N + ordinaryNativeExtra) (P + ep) (H + eh) (K + ek)
          uv oldHandle newHandle scs oldValue value caller before after memos.query readAfter checked.core heap action
          (readExact er) (checkExact ec) oldDecoded prepared raw encoded (adapted ei)]
        have actual := ordinaryRun ordinaryReadExtra ordinaryNativeExtra (P + ep) (H + eh) ek
          (Nat.le_add_right _ _) (Nat.le_add_right _ _)
        rw [show SourcePruningEnumerationNativeOrdinary.run checkEmpty (R + ordinaryReadExtra)
          (N + ordinaryNativeExtra) (P + ep) (H + eh) (K + ek) uv edgesOf
          (SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
          after memos.query = _ from (by simpa only [query] using actual)]

end MicroCFTA.SourcePruningEnumerationSelectedStep
