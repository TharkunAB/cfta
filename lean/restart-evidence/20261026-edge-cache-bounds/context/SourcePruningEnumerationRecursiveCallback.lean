import MicroCFTA.SourcePruningEnumerationRecursivePrefix
import MicroCFTA.SourcePruningEnumerationRecursiveEquations
import MicroCFTA.SourcePruningCallbackCompletion

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationOrder EnumerationCompressionFrame
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningRecordTypes SourcePruningPartialMatch
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
variable (caller : Caller width) (memos : Memos) (before : Cached)
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- Current callback invariants derive its exact result, returned packet and concrete continuation. -/
theorem callback_complete (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment) :
    ∃ fuel result after,
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result) stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before)) := by
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  obtain ⟨fuel, result, after, success, stable, frame, afterOrder, types, holes, typing, bounded⟩ :=
    recordTypes_inl_complete_bounded graph templates level frontier metadata uv fragment before.core
      packet.safe ordered allocated packet.bounded
  refine ⟨fuel, result, after,
    callback_frame packet result.2 after stable.safe frame ⟨level, frontier, afterOrder⟩ bounded,
    stable, frame, types, holes, typing, ?_⟩
  intro extra
  have more := recordTypes_moreFuel graph templates fuel extra metadata uv (.inl fragment)
    before.core result after success
  refine ⟨more, SourcePruningCallbackExact.recordTypes_exact graph templates (fuel + extra) metadata uv
    (.inl fragment) before.core after result more, ?_⟩
  intro recur stop order
  exact continueWith_exact recur graph templates stop order (fuel + extra) metadata uv fragment
    caller memos.query before result after more

variable [DecidableEq Symbol] [DecidableEq Node]

/-- One work bound supports the actual callback and its next accepted selected prefix. -/
theorem callback_prefix_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (checkEmpty : Bool) (edgesOf : Node → List (InternedConstructorTemplates.EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment) :
    ∃ fuel result after,
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        (∀ recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
        (result.1 = false → ∀ selected,
          SourcePruningEnumerationRestart.decision stop order result.2
              (EnumerationExpandableIndex.frame after before) = some (.expand selected) →
          SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
            stop order result.2 formulas solver inventory (fuel + extra) selected caller
            (EnumerationExpandableIndex.frame after before) memos
            (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order result.2
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
              selected caller (EnumerationExpandableIndex.frame after before) memos.query)) := by
  obtain ⟨callbackFuel, result, after, returned, stable, frame, types, holes, typing, callback⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before packet allocated
  obtain ⟨prefixFuel, prefixReady⟩ := packet_prefix_complete holeKey fits admits graph templates checkEmpty edgesOf
    stop order result.2 formulas solver inventory caller memos (EnumerationExpandableIndex.frame after before) returned
  refine ⟨callbackFuel + prefixFuel, result, after, returned, stable, frame, types, holes, typing, ?_⟩
  intro extra
  have actual := callback (prefixFuel + extra)
  rw [← Nat.add_assoc] at actual
  refine ⟨actual.1, actual.2.1, (fun recur => actual.2.2 recur stop order), ?_⟩
  intro _accepted selected chosen
  have ready := prefixReady (callbackFuel + extra) selected chosen
  have same : prefixFuel + (callbackFuel + extra) = callbackFuel + prefixFuel + extra := by omega
  rw [same] at ready
  exact ready

end MicroCFTA.SourcePruningEnumerationRecursive
