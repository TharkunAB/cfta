import MicroCFTA.SourcePruningEnumerationBoundaryPrefixIdentity
import MicroCFTA.SourcePruningEnumerationBoundaryEntryBudget
import MicroCFTA.SourcePruningEnumerationChildShapeBudget
import MicroCFTA.SourcePruningEnumerationSelectedPreparation

/-!
# Actual boundary preparation consumes an original model budget

The complete prefix derives the checked handle and its fresh key.
The original packet then constructs actual entry and native preparation.
The returned expansion history consumes that key's finite shape budget.
Direct child allocation inherits the decrease at the same checked handle.
-/
namespace MicroCFTA.SourcePruningEnumerationBoundaryPreparationBudget
open Language EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationOrigins
open SourcePruningEnumerationModelKeyShapes SourcePruningEnumerationKeyShapeBudget
open SourcePruningEnumerationSelectedStep (runPrefix PrefixValid)
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

section Observed
variable [DecidableEq Symbol] [DecidableEq Node]

/-- Original inputs construct actual preparation and strict expansion and child budgets at a reached boundary. -/
theorem narrowed_boundary_preparation_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (checked : Core) (value : Node) (selectedAction : EnumerateM Symbol Constraint Unit)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (reached : Caller width) (queries : SourceEndpointMemo.Memos)
    (actionRaw : Option (List (Except Error (Unit × Core))))
    (after : Cached) (updated : Metadata Typing) (rightCore : Core)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query))
    (observed : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before memos.query =
        .narrowed checked (.done (value, some selectedAction) heap) reached queries actionRaw (some after)
          (some [.ok ((false, updated), rightCore)]) none)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
    (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment before.core)
    (origins : AssignmentOrigins whole before.core.counter assignment)
    (canonical : EnumerationValidity.Canonical before.core) :
    reached = caller ∧ queries = memos.query ∧
      ∃ (handle : Nat) (scs : List Suspended) (bound : Nat) (result : Node)
        (nextHeap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
        before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
        (∀ extra, SourcePruningEnumerationSelectedPreparation.run (bound + extra) (bound + extra)
          uv caller after =
          ([.ok ((uv, handle, scs, value), entered.core)], some (.done result nextHeap))) ∧
        Packet formulas solver inventory
          (SourcePruningEnumerationSelectedValueCaller.advance caller nextHeap) memos metadata entered ∧
        EnumerationDriver.RenderStable after.core entered.core ∧
        entered.core.recursionAncestry = before.core.recursionAncestry ∧
        entered.core.expansionAncestry =
          (recursionKey handle scs :: before.core.recursionAncestry uv).eraseDups ∧
        (unused (keyShapes whole) handle entered.core.expansionAncestry).length <
          (unused (keyShapes whole) handle (before.core.recursionAncestry uv)).length ∧
        ∀ (allocationHeap : InternedConstructorTemplates.State Symbol Constraint)
          (node : Option Nat) (fresh : Nat) (child : Cached),
          SourcePruningEnumerationCachedChild.allocate allocationHeap node entered = some (fresh, child) →
          (unused (keyShapes whole) handle (child.core.recursionAncestry fresh)).length <
            (unused (keyShapes whole) handle (before.core.recursionAncestry uv)).length := by
  obtain ⟨_heapSame, reachedSame, queriesSame, _pure, _raw, cacheSame, _metadataSame, _rightSame,
    afterPacket, afterReady, handle, scs, readAfter, originalStored, _readStored, afterStored,
    originalDecoded, _encoded, _reading, checking, readFrame, _resolved, fresh⟩ :=
    SourcePruningEnumerationSelectedStep.narrowed_boundary_identity holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos checked
      value selectedAction heap reached queries actionRaw after updated rightCore packet chosen valid observed boundary
  obtain ⟨bound, decoded, result, nextHeap, entered, preparing, enteredDecoded, _post,
    enteredPacket, stable, _ready, _stored, _counter, _values, _flags, _waiting,
    _available, _closed, _language, _models⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete formulas solver inventory caller memos metadata
      after uv handle scs afterPacket afterReady afterStored
  have decodedSame : decoded = value := Option.some.inj (enteredDecoded.symm.trans originalDecoded)
  have actualEntry : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      bound uv after.core) = [.ok ((uv, handle, scs, value), entered.core)] := by
    have raw := congrArg Prod.fst (preparing 0)
    change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      (bound + 0) uv after.core) = [.ok ((uv, handle, scs, decoded), entered.core)] at raw
    simpa only [Nat.add_zero, decodedSame] using raw
  have entrySuccess : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      bound uv) after.core (uv, handle, scs, value) entered.core := by
    rw [Success, actualEntry]
    exact List.mem_singleton_self _
  obtain ⟨_size, _path, _lookup, histories, expansion⟩ :=
    SourcePruningEnumerationEntry.enter_history caller.checked.native.machine.heap bound uv
      after.core entered.core uv handle scs value afterPacket.safe.1.total entrySuccess
  have checkingSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      fuel uv handle scs) readAfter false checked := by
    rw [Success, checking]
    exact List.mem_singleton_self _
  have checkedFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
    caller.checked.native.machine.heap fuel uv handle scs readAfter checked
    (readFrame.total packet.safe.1.total) checkingSuccess
  have prefixFrame : Frame before.core after.core := by
    rw [cacheSame]
    exact readFrame.trans checkedFrame
  have expansionSame : entered.core.expansionAncestry =
      (recursionKey handle scs :: before.core.recursionAncestry uv).eraseDups := by
    simpa only [boundary, ↓reduceIte, prefixFrame.recursionAncestry] using expansion
  have readyBefore := SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory
    stop order metadata caller memos before uv packet chosen
  have member := stored_recursion_key_mem language meaning before.core whole assignment
    satisfied origins canonical readyBefore.inside originalStored
  have originallyFresh : recursionKey handle scs ∉ before.core.recursionAncestry uv := by
    simpa only [prefixFrame.recursionAncestry] using fresh
  have decreased : (unused (keyShapes whole) handle entered.core.expansionAncestry).length <
      (unused (keyShapes whole) handle (before.core.recursionAncestry uv)).length := by
    rw [expansionSame]
    exact unused_insert_lt (keyShapes whole) (recursionKey handle scs)
      (before.core.recursionAncestry uv) member originallyFresh
  refine ⟨reachedSame, queriesSame, handle, scs, bound, result, nextHeap, entered,
    originalStored, ?_, enteredPacket, stable, histories.trans prefixFrame.recursionAncestry,
    expansionSame, decreased, ?_⟩
  · intro extra
    simpa only [decodedSame] using preparing extra
  · intro allocationHeap node freshSlot child allocated
    exact Nat.lt_of_le_of_lt
      (SourcePruningEnumerationCachedChild.allocate_unused_le (keyShapes whole) handle
        allocationHeap node entered child freshSlot allocated).2 decreased


end Observed

/-- An original packet derives the prefix bound and actual boundary preparation budget without a validity supplier. -/
theorem packet_boundary_preparation_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (before : Cached) (memos : Memos)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
    (whole : Term Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment before.core)
    (origins : AssignmentOrigins whole before.core.counter assignment)
    (canonical : EnumerationValidity.Canonical before.core) :
    ∃ prefixBound, ∀ (extra uv : Nat) (checked : Core) (value : Node)
      (selectedAction : EnumerateM Symbol Constraint Unit)
      (heap : InternedConstructorTemplates.State Symbol Constraint)
      (reached : Caller width) (queries : SourceEndpointMemo.Memos)
      (actionRaw : Option (List (Except Error (Unit × Core))))
      (after : Cached) (updated : Metadata Typing) (rightCore : Core),
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv) →
      runPrefix holeKey fits admits graph templates stop order metadata
        (prefixBound + extra) (prefixBound + extra) (prefixBound + extra)
        (prefixBound + extra) (prefixBound + extra) (prefixBound + extra) uv caller before memos.query =
        .narrowed checked (.done (value, some selectedAction) heap) reached queries actionRaw (some after)
          (some [.ok ((false, updated), rightCore)]) none →
      MergedOrdinaryHeight.recursiveBoundary value = true →
      reached = caller ∧ queries = memos.query ∧
        ∃ (handle : Nat) (scs : List Suspended) (bound : Nat) (result : Node)
          (nextHeap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
          before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
          (∀ extra, SourcePruningEnumerationSelectedPreparation.run (bound + extra) (bound + extra)
            uv caller after =
            ([.ok ((uv, handle, scs, value), entered.core)], some (.done result nextHeap))) ∧
          Packet formulas solver inventory
            (SourcePruningEnumerationSelectedValueCaller.advance caller nextHeap) memos metadata entered ∧
          EnumerationDriver.RenderStable after.core entered.core ∧
          entered.core.recursionAncestry = before.core.recursionAncestry ∧
          entered.core.expansionAncestry =
            (recursionKey handle scs :: before.core.recursionAncestry uv).eraseDups ∧
          (unused (keyShapes whole) handle entered.core.expansionAncestry).length <
            (unused (keyShapes whole) handle (before.core.recursionAncestry uv)).length ∧
          ∀ (allocationHeap : InternedConstructorTemplates.State Symbol Constraint)
            (node : Option Nat) (fresh : Nat) (child : Cached),
            SourcePruningEnumerationCachedChild.allocate allocationHeap node entered = some (fresh, child) →
            (unused (keyShapes whole) handle (child.core.recursionAncestry fresh)).length <
              (unused (keyShapes whole) handle (before.core.recursionAncestry uv)).length := by
  classical
  obtain ⟨prefixBound, complete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      caller memos before packet
  refine ⟨prefixBound, ?_⟩
  intro extra uv checked value selectedAction heap reached queries actionRaw after updated rightCore
    chosen observed boundary
  exact narrowed_boundary_preparation_budget holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory
    (prefixBound + extra) uv caller before memos checked value selectedAction heap reached queries actionRaw
    after updated rightCore packet chosen (complete extra uv chosen) observed boundary language meaning
    whole assignment satisfied origins canonical

end MicroCFTA.SourcePruningEnumerationBoundaryPreparationBudget
