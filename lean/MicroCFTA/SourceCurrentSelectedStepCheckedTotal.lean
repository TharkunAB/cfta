import MicroCFTA.SourceCurrentSelectedStepCheckedFrame

namespace MicroCFTA.SourceCurrentSelectedStepCheckedTotal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
variable [DecidableEq Symbol] [DecidableEq Node]

attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Retain the selected-step result and derive totality for its checked core. -/
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
        let observed := SourcePruningEnumerationSelectedStep.run holeKey fits admits graph templates
          checkEmpty edgesOf stop order metadata (readFuel + er) (checkFuel + ec) nativeFuel
          representativeFuel (indexFuel + ei) callbackFuel r n p h k uv caller before memos.query
        SourcePruningEnumerationSelectedStep.Valid holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (readFuel + er) (checkFuel + ec) nativeFuel
          representativeFuel (indexFuel + ei) callbackFuel r n p h k uv caller before memos observed ∧
        match observed with
        | .narrowed checked _ _ _ _ _ _ _ =>
            Frame before.core checked ∧ UnionFind.Total checked.representatives
        | _ => True := by
  have originalTotal : UnionFind.Total before.core.representatives := by
    intro slot
    rcases paths slot with ⟨size, reaches⟩
    exact ⟨roots slot, size, reaches⟩
  obtain ⟨readFuel, checkFuel, nativeFuel, representativeFuel, indexFuel, results⟩ :=
    SourceCurrentSelectedStepCheckedFrame.complete holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory caller memos before
      preference uv roots initial safe pending selection realized paths counts flags
  refine ⟨readFuel, checkFuel, nativeFuel, representativeFuel, indexFuel, ?_⟩
  intro er ec ei callbackFuel r n p h k
  have previous := results er ec ei callbackFuel r n p h k
  refine ⟨previous.1, ?_⟩
  have frame := previous.2
  generalize observed : SourcePruningEnumerationSelectedStep.run holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata (readFuel + er) (checkFuel + ec) nativeFuel
    representativeFuel (indexFuel + ei) callbackFuel r n p h k uv caller before memos.query =
      produced at frame ⊢
  cases produced <;> try exact True.intro
  exact ⟨frame, EnumerationCompressionFrame.Frame.total frame originalTotal⟩

end MicroCFTA.SourceCurrentSelectedStepCheckedTotal
