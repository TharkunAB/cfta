import MicroCFTA.SourcePruningEnumerationRecursiveCallback
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# Assignment meaning of the actual fragment callback

The original callback supplies its actual returned frame and metadata.
That frame preserves complete assignments at the unchanged native heap.
The supplied continuation retains its original execution equation.
No semantic property of that continuation is an input.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationOrder EnumerationCompressionFrame
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningRecordTypes SourcePruningPartialMatch
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
variable (caller : Caller width) (memos : Memos) (before : Cached)
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- The full actual callback packet also preserves complete assignment meaning. -/
theorem callback_complete_semantics (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment) :
    ∃ fuel result after,
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result) stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap) residualMeaning assignment
          (EnumerationExpandableIndex.frame after before).core ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap) residualMeaning assignment before.core := by
  obtain ⟨fuel, result, after, returned, stable, framed, types, holes, typing, running⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before packet allocated
  refine ⟨fuel, result, after, returned, stable, framed, types, holes, typing, running, ?_⟩
  intro ambient residualMeaning assignment
  exact SourcePruningEnumerationNativeLanguage.satisfies_frame
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
    residualMeaning assignment before.core after framed

end MicroCFTA.SourcePruningEnumerationRecursive
