import MicroCFTA.SourceCurrentRecursiveObservationOrigins
import MicroCFTA.SourceCurrentRecursiveEntryPublicationSites
import MicroCFTA.SourceCurrentClassFoldEventPublications
import MicroCFTA.SourceCurrentProjectionPathOrigins

/-!
# Publication histories at selected recursive event observations

Actual ordinary prefixes retain the publication history of the same
captured event heap. Its native or Head execution stays at that heap.
The selected observation retains the exact full row and residual path.
The physical row-origin view remains separate from the native reader.
-/
namespace MicroCFTA.SourceCurrentRecursiveEventPublications
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

local notation "Heap" => State Symbol Guard
local notation "PublicationHistory" => SourceCurrentNativeMuPublication.History
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {sourceHeap : Heap}

/-- Actual selected recursive observations retain the same event publication history and path origins. -/
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
    (published : PublicationHistory sourceHeap before.native.machine.heap)
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
      ∃ located : Entry project read position row initialPath needle,
      SourceCurrentClassFoldStructuralOrigins.FoldEvent formulas solver actual forestIndex event ∧
      Occurs event residual needle ∧
      ∃ observation : Observation needle row,
        path.map Int.ofNat = initialPath.map Int.ofNat ++ observation.path ∧
        Keeps after.native.machine.heap observation.before ∧ Keeps observation.reader reader ∧
        SourceCurrentClassEventPublications.Source (width := width) formulas solver sourceHeap event observation.before ∧
        SourceCurrentRecursiveEntryPublicationSites.Site located observation.before ∧
        Keeps observation.before observation.readAfter ∧
        SourceCurrentProjectionPathOrigins.PathOrigin observation.readAfter
          (residual.map Int.ofNat ++ observation.path) event row := by
  obtain ⟨next,receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads
    coherent active ready admitted available domains stored covered valid
  rcases SourceCurrentRecursiveObservationOrigins.fold_positive reads inventory coherent active ready admitted
      available domains stored covered valid history forestIndex value selected path observationDomain project read
      position row observed preparation initialSemantic initialCosts initialAvailable initialGuards preparationSafe normal
      gate guards readerSemantic later readerGuards nonplain with ordinary | recursive
  · exact .inl ordinary
  · obtain ⟨initialPath,needle,event,residual,entry,eventAt,occurrence⟩ := recursive
    obtain ⟨observation,splitPath,first,last,initialInterval,site⟩ := SourceCurrentRecursiveEntryPublicationSites.entry entry
      receipt.ready.semantic receipt.ready.costs (receipt.available value (List.mem_of_getElem? selected)) guards
      readerSemantic readerCosts later readerGuards
    have captured := SourceCurrentClassFoldEventPublications.fold reads inventory coherent active ready admitted
      available domains stored covered valid history published eventAt
    have source := captured.later first initialInterval
    have pathOrigin := SourceCurrentProjectionPathOrigins.project_read observation.project observation.read
      observation.position row observation.spine observation.semantic observation.costs observation.available
      observation.readerSemantic observation.readerCosts observation.later observation.readAfter (grows_refl _)
    have ancestry := SourceCurrentProjectionPathOrigins.occurs occurrence pathOrigin
    have projectEffects := SourceEqualityProjectionCosts.project_effects observation.project
      observation.semantic observation.costs observation.available
    have readEffects := SourceEqualityProjectionCosts.read_effects observation.read
      observation.readerSemantic observation.readerCosts observation.readerAvailable
    exact .inr ⟨initialPath,needle,event,residual,entry,eventAt,occurrence,
      observation,splitPath,first,last,source,site,projectEffects.1.trans (observation.later.trans readEffects.1),ancestry⟩

end MicroCFTA.SourceCurrentRecursiveEventPublications
