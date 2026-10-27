import MicroCFTA.SourcePruningEnumerationRecursiveCallback
import MicroCFTA.EnumerationValidity

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationOrder EnumerationCompressionFrame EnumerationValidity
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

/-!
# Valid stored tries after the actual recursive callback

The existing producer supplies its full execution and returned packet.
Its exact value-list frame retains the original trie invariant.
-/

/-- The complete callback receipt also retains valid stored tries from its original input. -/
theorem callback_complete_canonical (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (canonical : Canonical before.core) :
    ∃ fuel result after,
      (Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
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
                (EnumerationExpandableIndex.frame after before))) ∧ Canonical after := by
  obtain ⟨fuel, result, after, returned, stable, frame, types, holes, typing, running⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before packet allocated
  refine ⟨fuel, result, after, ⟨returned, stable, frame, types, holes, typing, running⟩, ?_⟩
  intro value member
  exact canonical value (by simpa only [frame.values] using member)

end MicroCFTA.SourcePruningEnumerationRecursive
