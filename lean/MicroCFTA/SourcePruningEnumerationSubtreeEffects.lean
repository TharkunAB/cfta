import MicroCFTA.SourcePruningEnumerationOutcomeResources

/-!
# Native effects from a recursive subtree

A completed subtree supplies the actual caller and full memos for the next
sibling. The captured cache and metadata retain their packet there. A stopped
subtree keeps its outputs, nested reason and actual optional endpoint.
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
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "FoldResult" => SourcePruningEnumerationNativeContinuations.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A completed subtree retains the captured sibling packet at its actual native endpoint. -/
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
  exact ⟨next, final, post, query.symm, captured_post packet post, bounded, known, outputPackets⟩

/-- Finish retains arbitrary stopped subtree outputs and never fills an absent endpoint. -/
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

end MicroCFTA.SourcePruningEnumerationRecursive
