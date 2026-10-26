import MicroCFTA.SourcePruningEnumerationCallbackOneResources
import MicroCFTA.SourcePruningEnumerationMassForecast

/-!
# A callback reservation fixed before the edge cache exists

The original mass ceiling pays the callback's actual depth-one expansion.
The complete earlier callback result remains available. The same outcome
also fits the larger reservation computed from that ceiling.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
local notation "narrowSeed" => SourcePruningEnumerationExpansionAdmission.narrowSeed
local notation "forecastCount" => SourcePruningEnumerationExpansionAdmission.count
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- An original mass ceiling derives the full callback result and one uniform resource bound. -/
theorem callback_one_complete_mass_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (ceiling : Nat)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : Reserved bits (narrowSeed seed)
      (SourcePruningEnumerationOriginalForecast.count (narrowSeed seed) ceiling)) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core) (outcome : Result),
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) 1)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (reservationAdvance (narrowSeed seed) (forecastCount seed before.core)) outcome ∧
      OutcomeResources formulas solver caller
        (reservationAdvance (narrowSeed seed)
          (SourcePruningEnumerationOriginalForecast.count (narrowSeed seed) ceiling)) outcome := by
  have actualReserved := SourcePruningEnumerationExpansionAdmission.reserved_of_mass
    bits seed before.core ceiling mass reserved
  obtain ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing,
    callback, running, resources⟩ := callback_one_complete_resources
      holeKey fits admits formulas solver inventory graph templates metadata uv fragment caller memos before
      checkEmpty edgesOf stop order seed packet allocated bounded known selectionMembers selectionLength actualReserved
  have counts := SourcePruningEnumerationExpansionAdmission.count_le_mass seed before.core ceiling mass
  have numeric := SourcePruningEnumerationIncomingReservation.advance_count_profile_mono (narrowSeed seed) counts
  have alphabet := SourcePruningEnumerationIncomingReservation.advance_count_alphabet_mono (narrowSeed seed) counts
  exact ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing,
    callback, running, resources, resources.mono numeric alphabet⟩

end MicroCFTA.SourcePruningEnumerationRecursive
