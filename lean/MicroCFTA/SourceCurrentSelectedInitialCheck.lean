import MicroCFTA.SourceCurrentSelectedNoHistoryCheck

/-! The original initial cache supplies the selected prefix input identities. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentSelectedInitialCheck
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

/-- The literal initial cache supplies the history, slot and root identities. -/
theorem selected_initial
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (graph : Graph Symbol Constraint) (root : Nat) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (initial : Context formulas solver inventory caller memos) (safe : Safe (EnumerationExpandableIndex.initial graph root).core)
    (pending : EnumerationReferences.PendingReferences (EnumerationExpandableIndex.initial graph root).core)
    (selection : EnumerationPureSelection.next preference (EnumerationExpandableIndex.initial graph root) = .expand uv)
    (realized : PendingRealized caller.checked.native.machine.heap (EnumerationExpandableIndex.initial graph root).core)
    (paths : Roots (EnumerationExpandableIndex.initial graph root).core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots (EnumerationExpandableIndex.initial graph root).core.values (EnumerationExpandableIndex.initial graph root).waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      (((EnumerationExpandableIndex.initial graph root).core.values[slot]?).getD .eliminated) = some ((EnumerationExpandableIndex.initial graph root).expandable slot))
    :
    ∃ (readFuel oldHandle : Nat) (scs : List Suspended) (oldValue : Node)
      (readAfter : Core) (checkFuel : Nat) (checked : Cached)
      (nativeFuel representativeFuel : Nat) (result : Node)
      (heap : InternedConstructorTemplates.State Symbol Constraint) (final : Memos)
      (action : EnumerateM Symbol Constraint Unit),
      uv = 0 ∧ oldHandle = root ∧ scs = [] ∧
      (EnumerationExpandableIndex.initial graph root).core.values[uv]? = some (.unenumerated (some oldHandle) scs) ∧
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv (EnumerationExpandableIndex.initial graph root).core) =
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
          uv caller (EnumerationExpandableIndex.initial graph root) memos.query with
        | .narrowed actualChecked prepared reached queries _ _ _ ordinary =>
            actualChecked = checked.core ∧ prepared = .done (result, some action) heap ∧
            reached = SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge ∧
            queries = memos.query ∧ ordinary = none
        | _ => False) := by
  obtain ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, checked,
      nativeFuel, representativeFuel, result, heap, final, action, stored, rest⟩ :=
    SourceCurrentSelectedNoHistoryCheck.selected_without_target_history
      formulas solver inventory caller memos holeKey fits admits metadata graph templates checkEmpty edgesOf
      stop order (EnumerationExpandableIndex.initial graph root) preference uv roots
      initial safe pending selection realized paths counts flags (by rfl)
  have slotFacts : uv = 0 ∧ oldHandle = root ∧ scs = [] := by
    cases uv with
    | zero =>
        change (some (.unenumerated (some root) []) : Option (UVarValue Symbol)) =
          some (.unenumerated (some oldHandle) scs) at stored
        cases stored
        exact ⟨rfl, rfl, rfl⟩
    | succ next =>
        change (none : Option (UVarValue Symbol)) = some (.unenumerated (some oldHandle) scs) at stored
        cases stored
  exact ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, checked,
    nativeFuel, representativeFuel, result, heap, final, action,
    slotFacts.1, slotFacts.2.1, slotFacts.2.2, stored, rest⟩

end MicroCFTA.SourceCurrentSelectedInitialCheck
