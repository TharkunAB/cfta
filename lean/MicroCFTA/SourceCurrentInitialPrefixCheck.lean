import MicroCFTA.SourceCurrentInitialNextCheck
import MicroCFTA.SourceCurrentSelectedInitialCheck

/-! The literal initial selector supplies the endpoint for the checked prefix. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentInitialPrefixCheck
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

/-- Original input gates select an endpoint for the checked initial prefix. -/
theorem initial_prefix_of_pending
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (graph : Graph Symbol Constraint) (root : Nat) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (roots : Nat → Nat) (value : Node)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Language.Term Symbol → Prop)
    (assignment : Nat → Language.Term Symbol)
    (initial : Context formulas solver inventory caller memos)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller
      (EnumerationExpandableIndex.initial graph root))
    (safe : Safe (EnumerationExpandableIndex.initial graph root).core)
    (proper : EnumerationProgress.ProperState
      (EnumerationState.initial root : Core))
    (decoded : lookupNode caller.checked.native.machine.heap root = some value)
    (work : MergedOrdinaryHeight.recursiveBoundary value = false)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles
        (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
      residualMeaning assignment (EnumerationState.initial root))
    (pending : EnumerationReferences.PendingReferences (EnumerationExpandableIndex.initial graph root).core)
    (realized : PendingRealized caller.checked.native.machine.heap (EnumerationExpandableIndex.initial graph root).core)
    (paths : Roots (EnumerationExpandableIndex.initial graph root).core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots (EnumerationExpandableIndex.initial graph root).core.values (EnumerationExpandableIndex.initial graph root).waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      (((EnumerationExpandableIndex.initial graph root).core.values[slot]?).getD .eliminated) = some ((EnumerationExpandableIndex.initial graph root).expandable slot)) :
    ∃ uv,
      EnumerationPureSelection.next (order metadata) (EnumerationExpandableIndex.initial graph root) = .expand uv ∧
      EnumerationDriver.Ready uv (EnumerationState.initial root : Core) ∧
      EnumerationReferences.IncomingAvoid uv (EnumerationState.initial root : Core) ∧
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
  obtain ⟨uv, selection, ready, incoming⟩ :=
    SourcePruningEnumerationRestart.initial_next_of_pending formulas solver order metadata caller
      graph root value ambient residualMeaning assignment valid safe proper decoded work satisfied
  exact ⟨uv, selection, ready, incoming,
    SourceCurrentSelectedInitialCheck.selected_initial formulas solver inventory caller memos
      holeKey fits admits metadata graph root templates checkEmpty edgesOf stop order (order metadata)
      uv roots initial safe pending selection realized paths counts flags⟩

end MicroCFTA.SourceCurrentInitialPrefixCheck
