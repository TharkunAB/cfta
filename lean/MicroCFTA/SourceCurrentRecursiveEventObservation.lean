import MicroCFTA.SourceCurrentRecursiveObservationOrigins
import MicroCFTA.SourceCurrentRecursiveEntryObservation
import MicroCFTA.SourceCurrentClassFoldEventExecutions

/-!
# Captured event executions at a supported recursive observation

Actual preparation, class edits and selected observation retain the exact
recursive value. Its event supplies a captured native or Head execution.
Actual intervals connect that event heap to the recursive observation.
Native memo cells remain at their captured query return. Heap retention
alone does not transfer their history to the later observation reader.
-/
namespace MicroCFTA.SourceCurrentRecursiveEventObservation
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityRequiredGraph
open SourceCurrentProjectionRecursiveEntry (Entry)
open SourceCurrentClassRecursiveValueOrigins (Occurs)
open SourceCurrentPositiveProjectionSourceRoute (Route)
open SourceCurrentRecursiveEntryObservation (Observation)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A nonplain recursive observation retains its actual event execution and supported remaining read. -/
theorem fold {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {records inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Fold (width := width) records inputs before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.FoldReads formulas solver actual memos final)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : InternedNestedProvenance.Values before.native.machine.heap inputs)
    (domains : ∀ record ∈ records, ∀ own ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (own.map Int.ofNat) inputs)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (history : SourceCurrentNativeEdgeWriterGrowth.History before)
    (forestIndex : Nat) (value : Node) (selected : results[forestIndex]? = some value)
    (path : EqualityNormalize.Path) (observationDomain : SourceEqualityProjectionPathDomain.ForestClosed (Int.ofNat forestIndex :: path.map Int.ofNat) inputs)
    {projected projectAfter} (project : Project (path.map Int.ofNat) value after.native.machine.heap projected projectAfter)
    {reader rows readAfter} (read : Read projected reader rows readAfter)
    (position : Nat) (row : Row) (observed : rows[position]? = some row)
    {originals initialHeap preparedAfter entries}
    (preparation : RequireChildren entries 0 originals initialHeap inputs preparedAfter)
    (initialSemantic : SemanticReady initialHeap) (initialCosts : InternedFreshOrdinaryCostHeap.Heap initialHeap)
    (initialAvailable : InternedNestedProvenance.Values initialHeap originals) (initialGuards : Guards initialHeap)
    (preparationSafe : SourceCurrentRequiredRowOrigins.ChildrenSafe entries 0 originals)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal initialHeap)
    {gateAfter} (gate : EndpointStatefulGateTrace.PathTrace SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) originals (forestIndex :: path)
      initialHeap false gateAfter)
    (guards : Guards after.native.machine.heap)
    (readerSemantic : SemanticReady reader) (readerCosts : InternedFreshOrdinaryCostHeap.Heap reader) (later : Keeps projectAfter reader) (readerGuards : Guards reader)
    (nonplain : SourceMemoGate.plain row.entry.key.constraint = false) :
    Route (path.map Int.ofNat) value row ∨ ∃ initialPath needle event residual,
      Entry project read position row initialPath needle ∧
      SourceCurrentClassFoldStructuralOrigins.FoldEvent formulas solver actual forestIndex event ∧
      Occurs event residual needle ∧
      ∃ observation : Observation needle row,
        path.map Int.ofNat = initialPath.map Int.ofNat ++ observation.path ∧
        Keeps after.native.machine.heap observation.before ∧ Keeps observation.reader reader ∧
        SourceCurrentClassEventExecutions.Source (width := width) formulas solver event observation.before := by
  obtain ⟨next,receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads
    coherent active ready admitted available domains stored covered valid
  rcases SourceCurrentRecursiveObservationOrigins.fold_positive reads inventory coherent active ready admitted
      available domains stored covered valid history forestIndex value selected path observationDomain project read
      position row observed preparation initialSemantic initialCosts initialAvailable initialGuards preparationSafe normal
      gate guards readerSemantic later readerGuards nonplain with ordinary | recursive
  · exact .inl ordinary
  · obtain ⟨initialPath,needle,event,residual,entry,eventAt,occurrence⟩ := recursive
    obtain ⟨observation,splitPath,first,last⟩ := SourceCurrentRecursiveEntryObservation.entry entry
      receipt.ready.semantic receipt.ready.costs (receipt.available value (List.mem_of_getElem? selected)) guards
      readerSemantic readerCosts later readerGuards
    have source := SourceCurrentClassFoldEventExecutions.fold reads inventory coherent active ready admitted
      available domains stored covered valid history eventAt
    exact .inr ⟨initialPath,needle,event,residual,entry,eventAt,occurrence,observation,splitPath,first,last,
      source.later first⟩

end MicroCFTA.SourceCurrentRecursiveEventObservation
