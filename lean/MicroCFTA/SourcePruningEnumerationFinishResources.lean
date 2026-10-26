import MicroCFTA.SourcePruningEnumerationOutcomeResources
import MicroCFTA.SourcePruningEnumerationHookCertificates

/-!
# Resources for the actual finished alternative result

The finish operation retains the aggregate native prefix and each emitted
output. An unsupported edge has no runtime endpoint. An exhausted callback
retains its actual endpoint. The proof does not execute a continuation.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "FoldResult" => SourcePruningEnumerationNativeContinuations.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Exact scan witnesses retain resources after finish without filling an absent endpoint. -/
theorem finish_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (before : Cached) (uv : Nat) (scanSeed finalSeed : Seed)
    (scs : List Suspended) (edges : List (EdgeValue Symbol Constraint))
    (processed : List (Receipt width)) (outputs : List (Output width Typing))
    (afterCaller : Caller width) (next : Inventory) (final : Memos)
    (result : FoldResult (Output width Typing) (Failure width Typing) width)
    (post : Post formulas solver next original afterCaller final)
    (bounded : Fits finalSeed.2 afterCaller.checked)
    (known : Heap (fun guard => guard ∈ finalSeed.1) afterCaller.checked.native.machine.heap)
    (outputResources : ∀ output ∈ outputs, OutputResources formulas solver original finalSeed output)
    (shape : result = .complete processed outputs afterCaller final.query ∨
      ∃ current, result = .stopped processed outputs current ∧
        SourcePruningEnumerationNativeHookResources.StoppedAt formulas solver original before uv scanSeed
          scs edges processed.length afterCaller next final current) :
    OutcomeResources formulas solver original finalSeed (finish uv result) := by
  unfold OutcomeResources
  refine ⟨afterCaller, next, final, post, bounded, known, ?_⟩
  rcases shape with completed | ⟨current, stopped, certificate⟩
  · subst result
    exact ⟨rfl, rfl, outputResources⟩
  · subst result
    change (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) ∧
      ∀ output ∈ outputs, OutputResources formulas solver original finalSeed output
    refine ⟨?_, outputResources⟩
    rcases certificate with unsupported |
      ⟨_fragment, _receiptCache, _selected, _updated, _callbackCache, observation, _receipt, _packet⟩
    · rw [unsupported]
      exact .inl rfl
    · rw [observation]
      exact .inr rfl

end MicroCFTA.SourcePruningEnumerationRecursive
