import MicroCFTA.SourcePruningEnumerationSharedHookCertificates

/-!
# Native effects at actual shared subtree outcomes

A completed subtree retains the original captured sibling cache at its
returned caller and full memos. Each emitted output keeps its own cache.
Finish preserves the actual optional endpoint of a stopped subtree.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "FoldResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A completed actual subtree retains the captured sibling packet at the same endpoint. -/
theorem completed_captured_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (memos : Memos)
    (metadata : Metadata Typing) (before : Cached) (seed : Seed)
    (outputs : List (Output width Typing)) (reached : Caller width) (queries : Queries)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (resources : OutcomeResources formulas solver caller seed (.complete outputs reached queries)) :
    ∃ (next : Inventory) (final : Memos),
      Post formulas solver next caller reached final ∧ final.query = queries ∧
      Packet formulas solver next reached final metadata before ∧
      Fits seed.2 reached.checked ∧ Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
      ∀ output ∈ outputs, OutputResources formulas solver caller seed output := by
  obtain ⟨actual, next, final, post, bounded, known, same, query, outputPackets⟩ := resources
  subst actual
  exact ⟨next, final, post, query.symm,
    SourcePruningEnumerationRecursive.captured_post packet post, bounded, known, outputPackets⟩

/-- Finish retains stopped outputs and does not fill an absent native endpoint. -/
theorem finish_resources_general
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (uv : Nat) (seed : Seed)
    (processed : List (Receipt width)) (outputs : List (Output width Typing))
    (afterCaller : Caller width) (next : Inventory) (final : Memos)
    (result : FoldResult (Output width Typing) (Failure width Typing) width)
    (post : Post formulas solver next original afterCaller final)
    (bounded : Fits seed.2 afterCaller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) afterCaller.checked.native.machine.heap)
    (outputResources : ∀ output ∈ outputs, OutputResources formulas solver original seed output)
    (shape : result = .complete processed outputs afterCaller final.query ∨
      ∃ current, result = .stopped processed outputs current ∧
        (endpoint current = none ∨ endpoint current = some (afterCaller, final.query))) :
    OutcomeResources formulas solver original seed (finish uv result) := by
  refine ⟨afterCaller, next, final, post, bounded, known, ?_⟩
  rcases shape with completed | ⟨current, stopped, observed⟩
  · subst result
    exact ⟨rfl, rfl, outputResources⟩
  · subst result
    exact ⟨observed, outputResources⟩

end MicroCFTA.SourcePruningEnumerationSharedRecursive
