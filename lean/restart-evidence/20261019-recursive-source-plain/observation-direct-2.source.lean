import MicroCFTA.SourceCurrentRecursiveSourcePlain
import MicroCFTA.SourceCurrentRecursiveEntryPlainRead

/-!
# Event sources for nonplain recursive observations

Actual Required preparation and an original false gate exclude an initial
recursive source of a nonplain selected row. Actual fold effects and the
exact reader derive the source.
The ordinary alternative remains a route in the final fold value.
An event retains the exact recursive value and a literal residual path.
This result does not construct a projection of the whole event value.
-/
namespace MicroCFTA.SourceCurrentRecursiveObservationOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityRequiredGraph
open SourceCurrentProjectionRecursiveEntry (Entry)
open SourceCurrentClassRecursiveValueOrigins (Occurs)
open SourceCurrentPositiveProjectionSourceRoute (Route)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A nonplain selected observation has an ordinary final route or an actual event source. -/
theorem fold_positive {formulas : SourceGuards.Formulas FullSyntax.Formula}
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
    (readerSemantic : SemanticReady reader) (later : Keeps projectAfter reader) (readerGuards : Guards reader)
    (nonplain : SourceMemoGate.plain row.entry.key.constraint = false) :
    Route (path.map Int.ofNat) value row ∨ ∃ initialPath needle event residual,
      Entry project read position row initialPath needle ∧
      SourceCurrentClassFoldStructuralOrigins.FoldEvent formulas solver actual forestIndex event ∧
      Occurs event residual needle := by
  obtain ⟨next,receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads
    coherent active ready admitted available domains stored covered valid
  have preparedOrigins := SourceCurrentRequiredRowOrigins.children preparation initialSemantic initialCosts
    initialAvailable initialGuards preparationSafe
  rcases SourceCurrentProjectionRecursiveEntry.fold_first reads inventory coherent active ready admitted available
      domains stored covered valid history forestIndex value selected observationDomain project read position row observed
      with ordinary | recursive
  · exact .inl ordinary
  · obtain ⟨initialPath,needle,entry,ancestry⟩ := recursive
    rcases ancestry with original | event
    · obtain ⟨prepared,preparedSelected,occurrence⟩ := original
      have signed : select inputs (Int.ofNat forestIndex) = some prepared := by
        simpa only [select,Int.ofNat_eq_natCast,
          ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg _)),Int.toNat_natCast] using preparedSelected
      obtain ⟨original,sourceSelected,related⟩ := SourceEqualityProjectionLanguage.all₂_signed
        preparedOrigins (Int.ofNat forestIndex) prepared signed
      have originalSelected : originals[forestIndex]? = some original := by
        simpa only [select,Int.ofNat_eq_natCast,
          ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg _)),Int.toNat_natCast] using sourceSelected
      have located := SourceCurrentProjectionRecursiveEntry.occurs entry
      obtain ⟨residual,splitPath⟩ := located.2.2
      have natural : path = initialPath ++ residual.map Int.toNat := by
        have converted := congrArg (List.map Int.toNat) splitPath
        simpa only [List.map_append,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id_fun] using converted
      have nodeGate : EndpointStatefulGateTrace.NodeTrace SourceMemoGate.unconstrained
          (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) path original
          initialHeap false gateAfter := by
        cases gate with
        | child trace =>
          cases trace with
          | missing absent => rw [absent] at originalSelected; cases originalSelected
          | present found traced =>
            cases Option.some.inj (found.symm.trans originalSelected)
            exact traced
      have plain := SourceCurrentRecursiveSourcePlain.required initialSemantic normal
        (initialAvailable original (List.mem_of_getElem? originalSelected)) related occurrence located.2.1
        (residual.map Int.toNat) (natural ▸ nodeGate)
      have observedPlain := SourceCurrentRecursiveEntryPlainRead.entry Plain entry plain receipt.ready.semantic
        receipt.ready.costs (receipt.available value (List.mem_of_getElem? selected)) guards
        readerSemantic later readerGuards
      rw [nonplain] at observedPlain
      cases observedPlain
    · obtain ⟨event,residual,happened,occurrence⟩ := event
      exact .inr ⟨initialPath,needle,event,residual,entry,happened,occurrence⟩

end MicroCFTA.SourceCurrentRecursiveObservationOrigins
