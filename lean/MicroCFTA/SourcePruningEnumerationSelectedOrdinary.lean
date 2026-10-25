import MicroCFTA.SourcePruningEnumerationSelectedNarrow
import MicroCFTA.SourcePruningEnumerationRecursionOrder
import MicroCFTA.SourcePruningEnumerationNativeOrdinary
import MicroCFTA.SourcePruningEnumerationReceiptCallback

namespace MicroCFTA.SourcePruningEnumerationSelectedOrdinary
open Cache EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original selection reaches the actual narrowing endpoint and its admitted ordinary continuation. -/
theorem complete_with_history
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos)
    (safe : Safe before.core)
    (pending : EnumerationReferences.PendingReferences before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (readFuel oldHandle : Nat) (scs : List Suspended) (oldValue : Node)
      (readAfter : EnumerationState.State Symbol Constraint) (checkFuel : Nat) (repeated : Bool)
      (checked : EnumerationExpandableIndex.Cached Symbol Constraint),
      before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) ∧
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
      Available caller.checked.native.machine.heap oldValue ∧ oldValue.free = [] ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]) ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        (checkFuel + extra) uv oldHandle scs readAfter) = [.ok (repeated, checked.core)]) ∧
      EnumerationDriver.Ready uv checked.core ∧ Roots checked.core.representatives roots ∧
      PendingRealized caller.checked.native.machine.heap checked.core ∧
      EnumerationCanonicalWaiting.Correct roots checked.core.values checked.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((checked.core.values[slot]?).getD .eliminated) = some (checked.expandable slot)) ∧
      EnumerationReferences.IncomingAvoid uv checked.core ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences checked.core) ∧
      (repeated = true → MergedOrdinaryHeight.recursiveBoundary oldValue = true ∧
        checked.core.values[uv]? = some (.unenumerated (some oldHandle) []) ∧ checked.expandable uv = false ∧
        checked.waiting = EnumerationCanonicalWaiting.count roots (-1) scs before.waiting ∧
        ∃ (resolved : EnumerationState.State Symbol Constraint) (countFuel : Nat),
          Frame before.core resolved ∧ Success (representative checkFuel uv) readAfter uv resolved ∧
          recursionKey oldHandle scs ∈ resolved.recursionAncestry uv ∧
          Success (setValue uv (.unenumerated (some oldHandle) [])) resolved () checked.core ∧
          ∀ extra, SourcePruningEnumerationNativeIndex.write caller.checked.native.machine.heap
            (countFuel + extra) uv (.unenumerated (some oldHandle) []) [] scs
              (EnumerationExpandableIndex.frame resolved before) = some checked) ∧
      (repeated = false →
        ∃ (result : Node) (nativeFuel : Nat) (heap : InternedConstructorTemplates.State Symbol Constraint)
          (newHandle : Nat) (final : Memos),
          let afterCaller := SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge
          SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue caller.checked.native.machine.heap =
            .done result heap ∧
          (∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata (nativeFuel + extra) uv oldValue
            caller.checked.native.machine.heap = .done result heap) ∧
          Post formulas solver inventory caller afterCaller final ∧
          Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
          Available afterCaller.checked.native.machine.heap result ∧ result.free = [] ∧
          encodeNode result = some newHandle ∧ lookupNode afterCaller.checked.native.machine.heap newHandle = some result ∧
          (result = .empty → ∀ representativeFuel,
            SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
              scs oldValue caller.checked.native.machine.heap =
              .done (result, some (reject : EnumerateM Symbol Constraint Unit)) heap ∧
            ¬ ∃ after : EnumerationState.State Symbol Constraint,
              Success (reject : EnumerateM Symbol Constraint Unit) checked.core () after) ∧
          (result ≠ .empty →
            ∃ (representativeFuel countFuel : Nat) (action : EnumerateM Symbol Constraint Unit)
              (after : EnumerationExpandableIndex.Cached Symbol Constraint),
              SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
                scs oldValue caller.checked.native.machine.heap = .done (result, some action) heap ∧
              Success action checked.core () after.core ∧
              ((newHandle = oldHandle ∧ after = EnumerationExpandableIndex.frame checked.core before) ∨
                (newHandle ≠ oldHandle ∧ ∃ rereadAfter : EnumerationState.State Symbol Constraint,
                  Success (representative representativeFuel uv) checked.core uv rereadAfter ∧
                  Success (setValue uv (.unenumerated (some newHandle) scs)) rereadAfter () after.core ∧
                  ∀ extra, SourcePruningEnumerationNativeIndex.write afterCaller.checked.native.machine.heap
                    (countFuel + extra) uv (.unenumerated (some newHandle) scs) scs scs
                      (EnumerationExpandableIndex.frame rereadAfter before) = some after)) ∧
              after.waiting = before.waiting ∧ EnumerationDriver.Ready uv after.core ∧
              Roots after.core.representatives roots ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
              after.core.values[uv]? = some (.unenumerated (some newHandle) scs) ∧
              EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
              (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
                ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
              (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
              EnumerationReferences.IncomingAvoid uv after.core ∧
              (∀ callbackFuel, Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv (.inr newHandle))
                after.core (false, metadata) after.core) ∧
              ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
                (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
                (free : List InternedBinderProtocol.Reference),
                result = .node parentEntry storedEdges depth free →
                scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false →
                (∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), edge ∈ storedEdges) →
                SourcePruningEnumerationNativeOrdinary.Ranges checkEmpty uv edgesOf afterCaller after final.query →
                ∃ (r n p h k : Nat) (entered : EnumerationExpandableIndex.Cached Symbol Constraint)
                  (processed : List (SourcePruningEnumerationSelectedEdge.Result width))
                  (lastCaller : Caller width) (saved : SourceEndpointMemo.Memos) (last : Memos)
                  (next : Inventory) (ordinary : SourcePruningEnumerationNativeBranches.Result width),
                  (∀ er en P H ek, p ≤ P → h ≤ H →
                    SourcePruningEnumerationNativeOrdinary.run checkEmpty (r + er) (n + en) P H (k + ek)
                      uv edgesOf afterCaller after final.query =
                      ([.ok ((uv, newHandle, scs, .node parentEntry storedEdges depth free), entered.core)], some ordinary)) ∧
                  EnumerationDriver.RenderStable after.core entered.core ∧
                  entered.expandable = after.expandable ∧ entered.waiting = after.waiting ∧
                  Post formulas solver next caller lastCaller last ∧ last.query = saved ∧
                  (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Admitted uv receipt) ∧
                  (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Pending receipt) ∧
                  (∀ receipt ∈ processed,
                    ∃ (reached : Caller width) (savedQueries : SourceEndpointMemo.Memos)
                      (receiptInventory : Inventory) (receiptMemos : Memos),
                      SourcePruningEnumerationNativeBranches.advance receipt = some (reached, savedQueries) ∧
                      Post formulas solver receiptInventory caller reached receiptMemos ∧ receiptMemos.query = savedQueries) ∧
                  (∀ receipt ∈ processed,
                    SourcePruningEnumerationNativeBranchCompletion.FragmentHistory before.core receipt) ∧
                  (∀ receipt ∈ processed,
                    SourcePruningEnumerationReceiptCallback.Completes graph templates metadata uv before.core receipt) ∧
                  (ordinary = .complete processed lastCaller saved ∨ ordinary = .stopped processed (some .unhandled)) ∧
                  ((∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), arityAllows edge.children.length scs = true →
                    SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
                    ordinary = .complete processed lastCaller saved))) := by
  obtain ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored, oldDecoded,
    oldAvailable, oldClosed, readExact, checkExact, checkReady, checkPaths, checkRealized,
    checkCounts, checkFlags, checkIncoming, checkPending, parked, continued⟩ :=
    SourcePruningEnumerationSelectedNarrow.complete formulas solver inventory caller memos
      holeKey fits admits metadata graph templates before preference uv roots initial safe selection realized paths counts flags
  refine ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored, oldDecoded,
    oldAvailable, oldClosed, readExact, checkExact, checkReady, checkPaths, checkRealized, checkCounts,
    checkFlags, checkIncoming, checkPending, parked, ?_⟩
  intro notRepeated
  have read : Success (getValue readFuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter := by
    rw [Success, ← Nat.add_zero readFuel, readExact 0]
    exact List.mem_singleton_self _
  have firstFrame := (getValue_frame readFuel uv before.core readAfter _ safe.1.total read).1
  have check : Success (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      checkFuel uv oldHandle scs) readAfter repeated checked.core := by
    rw [Success, ← Nat.add_zero checkFuel, checkExact 0]
    exact List.mem_singleton_self _
  rw [notRepeated] at check
  have checkedFrame := firstFrame.trans
    (SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame _ checkFuel uv oldHandle scs
      readAfter checked.core (firstFrame.total safe.1.total) check)
  obtain ⟨result, nativeFuel, heap, newHandle, final, narrowed, stable, post, retained, query,
    available, closed, encoded, decoded, rejected, completed⟩ := continued notRepeated
  refine ⟨result, nativeFuel, heap, newHandle, final, narrowed, stable, post, retained, query,
    available, closed, encoded, decoded, rejected, ?_⟩
  intro nonempty
  obtain ⟨representativeFuel, countFuel, action, after, prepared, observed, shape, waiting, afterReady,
    afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, afterIncoming, callback⟩ := completed nonempty
  refine ⟨representativeFuel, countFuel, action, after, prepared, observed, shape, waiting, afterReady,
    afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, afterIncoming, callback, ?_⟩
  have prefixCounter : after.core.counter = before.core.counter := by
    rcases shape with ⟨_same, equal⟩ | ⟨_different, rereadAfter, reading, writing, _counted⟩
    · simpa only [equal, EnumerationExpandableIndex.frame] using checkedFrame.counter
    · have rereadFrame := representative_frame representativeFuel uv uv checked.core rereadAfter
        checkReady.safe.1.total reading
      have writtenShape := (EnumerationDriver.modify_success _ rereadAfter after.core).mp writing
      simpa only [writtenShape] using rereadFrame.counter.trans checkedFrame.counter
  have prefixOrder : ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
      EnumerationOrder.Stratified after.core level frontier := by
    intro level frontier ordered
    have checkedOrder := EnumerationOrder.frame_stratified before.core checked.core checkedFrame level frontier ordered
    rcases shape with ⟨_same, equal⟩ | ⟨_different, rereadAfter, reading, writing, _counted⟩
    · simpa only [equal, EnumerationExpandableIndex.frame] using checkedOrder
    · have rereadFrame := representative_frame representativeFuel uv uv checked.core rereadAfter
        checkReady.safe.1.total reading
      have oldStored : rereadAfter.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
        simpa only [rereadFrame.values, checkedFrame.values] using stored
      exact EnumerationOrder.setValue_pending_stratified uv (some oldHandle) (some newHandle) scs scs
        rereadAfter after.core oldStored level frontier
        (EnumerationOrder.frame_stratified checked.core rereadAfter rereadFrame level frontier checkedOrder) writing
  intro parentEntry storedEdges depth free parent nonterminal selected ranges
  have decodedParent := decoded
  rw [parent] at decodedParent
  have inputs := EnumerationReferences.pending_inputs after.core (afterPending pending) uv (some newHandle) scs afterStored
  obtain ⟨r, n, p, h, k, entered, processed, lastCaller, saved, last, next, ordinary,
    run, render, sameFlags, sameWaiting, lastPost, lastQuery, admitted, history, receiptPosts, fragments, ordinaryShape, supported⟩ :=
    SourcePruningEnumerationNativeOrdinary.complete_with_history formulas solver inventory _ after checkEmpty uv newHandle scs
      parentEntry storedEdges depth free edgesOf roots final post.context afterReady afterStored decodedParent
      afterRealized selected afterPaths afterCounts afterFlags inputs nonterminal ranges
  have initialFragments : ∀ receipt ∈ processed,
      SourcePruningEnumerationNativeBranchCompletion.FragmentHistory before.core receipt := by
    intro receipt member
    exact SourcePruningEnumerationNativeBranchCompletion.fragmentHistory_transport before.core after.core
      (Nat.le_of_eq prefixCounter.symm)
      (fun level frontier ordered => ⟨level, prefixOrder level frontier ordered⟩) receipt (fragments receipt member)
  refine ⟨r, n, p, h, k, entered, processed, lastCaller, saved, last, next, ordinary,
    run, render, sameFlags, sameWaiting, post.trans lastPost, lastQuery, admitted,
    history (afterPending pending) afterIncoming, ?_, initialFragments, ?_, ordinaryShape, supported⟩
  · intro receipt member
    obtain ⟨reached, savedQueries, receiptInventory, receiptMemos, reachedRun, receiptPost, receiptQueries⟩ :=
      receiptPosts receipt member
    exact ⟨reached, savedQueries, receiptInventory, receiptMemos, reachedRun, post.trans receiptPost, receiptQueries⟩
  · intro receipt member
    exact SourcePruningEnumerationReceiptCallback.completes graph templates metadata uv before.core receipt
      (admitted receipt member) (initialFragments receipt member)

/-- Original selection retains its admitted ordinary continuation and per-receipt Caller posts. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos)
    (safe : Safe before.core)
    (pending : EnumerationReferences.PendingReferences before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (readFuel oldHandle : Nat) (scs : List Suspended) (oldValue : Node)
      (readAfter : EnumerationState.State Symbol Constraint) (checkFuel : Nat) (repeated : Bool)
      (checked : EnumerationExpandableIndex.Cached Symbol Constraint),
      before.core.values[uv]? = some (.unenumerated (some oldHandle) scs) ∧
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
      Available caller.checked.native.machine.heap oldValue ∧ oldValue.free = [] ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]) ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        (checkFuel + extra) uv oldHandle scs readAfter) = [.ok (repeated, checked.core)]) ∧
      EnumerationDriver.Ready uv checked.core ∧ Roots checked.core.representatives roots ∧
      PendingRealized caller.checked.native.machine.heap checked.core ∧
      EnumerationCanonicalWaiting.Correct roots checked.core.values checked.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((checked.core.values[slot]?).getD .eliminated) = some (checked.expandable slot)) ∧
      EnumerationReferences.IncomingAvoid uv checked.core ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences checked.core) ∧
      (repeated = true → MergedOrdinaryHeight.recursiveBoundary oldValue = true ∧
        checked.core.values[uv]? = some (.unenumerated (some oldHandle) []) ∧ checked.expandable uv = false ∧
        checked.waiting = EnumerationCanonicalWaiting.count roots (-1) scs before.waiting ∧
        ∃ (resolved : EnumerationState.State Symbol Constraint) (countFuel : Nat),
          Frame before.core resolved ∧ Success (representative checkFuel uv) readAfter uv resolved ∧
          recursionKey oldHandle scs ∈ resolved.recursionAncestry uv ∧
          Success (setValue uv (.unenumerated (some oldHandle) [])) resolved () checked.core ∧
          ∀ extra, SourcePruningEnumerationNativeIndex.write caller.checked.native.machine.heap
            (countFuel + extra) uv (.unenumerated (some oldHandle) []) [] scs
              (EnumerationExpandableIndex.frame resolved before) = some checked) ∧
      (repeated = false →
        ∃ (result : Node) (nativeFuel : Nat) (heap : InternedConstructorTemplates.State Symbol Constraint)
          (newHandle : Nat) (final : Memos),
          let afterCaller := SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge
          SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue caller.checked.native.machine.heap =
            .done result heap ∧
          (∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata (nativeFuel + extra) uv oldValue
            caller.checked.native.machine.heap = .done result heap) ∧
          Post formulas solver inventory caller afterCaller final ∧
          Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
          Available afterCaller.checked.native.machine.heap result ∧ result.free = [] ∧
          encodeNode result = some newHandle ∧ lookupNode afterCaller.checked.native.machine.heap newHandle = some result ∧
          (result = .empty → ∀ representativeFuel,
            SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
              scs oldValue caller.checked.native.machine.heap =
              .done (result, some (reject : EnumerateM Symbol Constraint Unit)) heap ∧
            ¬ ∃ after : EnumerationState.State Symbol Constraint,
              Success (reject : EnumerateM Symbol Constraint Unit) checked.core () after) ∧
          (result ≠ .empty →
            ∃ (representativeFuel countFuel : Nat) (action : EnumerateM Symbol Constraint Unit)
              (after : EnumerationExpandableIndex.Cached Symbol Constraint),
              SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle
                scs oldValue caller.checked.native.machine.heap = .done (result, some action) heap ∧
              Success action checked.core () after.core ∧
              ((newHandle = oldHandle ∧ after = EnumerationExpandableIndex.frame checked.core before) ∨
                (newHandle ≠ oldHandle ∧ ∃ rereadAfter : EnumerationState.State Symbol Constraint,
                  Success (representative representativeFuel uv) checked.core uv rereadAfter ∧
                  Success (setValue uv (.unenumerated (some newHandle) scs)) rereadAfter () after.core ∧
                  ∀ extra, SourcePruningEnumerationNativeIndex.write afterCaller.checked.native.machine.heap
                    (countFuel + extra) uv (.unenumerated (some newHandle) scs) scs scs
                      (EnumerationExpandableIndex.frame rereadAfter before) = some after)) ∧
              after.waiting = before.waiting ∧ EnumerationDriver.Ready uv after.core ∧
              Roots after.core.representatives roots ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
              after.core.values[uv]? = some (.unenumerated (some newHandle) scs) ∧
              EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
              (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
                ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
              (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
              EnumerationReferences.IncomingAvoid uv after.core ∧
              (∀ callbackFuel, Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv (.inr newHandle))
                after.core (false, metadata) after.core) ∧
              ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
                (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
                (free : List InternedBinderProtocol.Reference),
                result = .node parentEntry storedEdges depth free →
                scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false →
                (∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), edge ∈ storedEdges) →
                SourcePruningEnumerationNativeOrdinary.Ranges checkEmpty uv edgesOf afterCaller after final.query →
                ∃ (r n p h k : Nat) (entered : EnumerationExpandableIndex.Cached Symbol Constraint)
                  (processed : List (SourcePruningEnumerationSelectedEdge.Result width))
                  (lastCaller : Caller width) (saved : SourceEndpointMemo.Memos) (last : Memos)
                  (next : Inventory) (ordinary : SourcePruningEnumerationNativeBranches.Result width),
                  (∀ er en P H ek, p ≤ P → h ≤ H →
                    SourcePruningEnumerationNativeOrdinary.run checkEmpty (r + er) (n + en) P H (k + ek)
                      uv edgesOf afterCaller after final.query =
                      ([.ok ((uv, newHandle, scs, .node parentEntry storedEdges depth free), entered.core)], some ordinary)) ∧
                  EnumerationDriver.RenderStable after.core entered.core ∧
                  entered.expandable = after.expandable ∧ entered.waiting = after.waiting ∧
                  Post formulas solver next caller lastCaller last ∧ last.query = saved ∧
                  (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Admitted uv receipt) ∧
                  (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Pending receipt) ∧
                  (∀ receipt ∈ processed,
                    ∃ (reached : Caller width) (savedQueries : SourceEndpointMemo.Memos)
                      (receiptInventory : Inventory) (receiptMemos : Memos),
                      SourcePruningEnumerationNativeBranches.advance receipt = some (reached, savedQueries) ∧
                      Post formulas solver receiptInventory caller reached receiptMemos ∧ receiptMemos.query = savedQueries) ∧
                  (ordinary = .complete processed lastCaller saved ∨ ordinary = .stopped processed (some .unhandled)) ∧
                  ((∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), arityAllows edge.children.length scs = true →
                    SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
                    ordinary = .complete processed lastCaller saved))) := by
  obtain ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored, oldDecoded,
    oldAvailable, oldClosed, readExact, checkExact, checkReady, checkPaths, checkRealized,
    checkCounts, checkFlags, checkIncoming, checkPending, parked, continued⟩ :=
    complete_with_history formulas solver inventory caller memos holeKey fits admits metadata graph templates
      checkEmpty edgesOf before preference uv roots initial safe pending selection realized paths counts flags
  refine ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored, oldDecoded,
    oldAvailable, oldClosed, readExact, checkExact, checkReady, checkPaths, checkRealized,
    checkCounts, checkFlags, checkIncoming, checkPending, parked, ?_⟩
  intro notRepeated
  obtain ⟨result, nativeFuel, heap, newHandle, final, narrowed, stable, post, retained, query,
    available, closed, encoded, decoded, rejected, completed⟩ := continued notRepeated
  refine ⟨result, nativeFuel, heap, newHandle, final, narrowed, stable, post, retained, query,
    available, closed, encoded, decoded, rejected, ?_⟩
  intro nonempty
  obtain ⟨representativeFuel, countFuel, action, after, prepared, observed, shape, waiting, afterReady,
    afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, afterIncoming, callback, ordinary⟩ :=
    completed nonempty
  refine ⟨representativeFuel, countFuel, action, after, prepared, observed, shape, waiting, afterReady,
    afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, afterIncoming, callback, ?_⟩
  intro parentEntry storedEdges depth free parent nonterminal selected ranges
  obtain ⟨r, n, p, h, k, entered, processed, lastCaller, saved, last, next, result,
    run, render, sameFlags, sameWaiting, lastPost, lastQuery, admitted, history, receiptPosts,
    _fragments, _callbacks, ordinaryShape, supported⟩ := ordinary parentEntry storedEdges depth free parent nonterminal selected ranges
  exact ⟨r, n, p, h, k, entered, processed, lastCaller, saved, last, next, result,
    run, render, sameFlags, sameWaiting, lastPost, lastQuery, admitted, history, receiptPosts, ordinaryShape, supported⟩

end MicroCFTA.SourcePruningEnumerationSelectedOrdinary
