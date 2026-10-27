import MicroCFTA.SourcePruningEnumerationAllocatedOriginArity
import MicroCFTA.SourcePruningEnumerationArityOrigins

/-!
# Edge-arity records after actual allocated constructors

The actual constructor receipt identifies its requested edge and final heap.
Its returned coherent record supplies the requested guard and child count.
The constructor's projected arity then checks the newly requested key.
All earlier edge-key checks survive the actual insertion.
Parent local reduction needs a separate invariant at its reached middle heap.
-/
namespace MicroCFTA.SourceCurrentAllocatedMkEdge
open Cache InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => SourcePruningEnumerationArityOrigins.Heap
local notation "Fits" => SourcePruningEnumerationArityOrigins.Fits
variable {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

private theorem makeEdge_record
    (symbol : Symbol) (constraint : Constraint) (children : List (Value Symbol Constraint))
    (before after : State Symbol Constraint) (edge : EdgeValue Symbol Constraint)
    (observed : run (makeEdge symbol constraint children) before = (edge, after)) :
    after.edgeRecords ⟨symbol, children.map Value.referenceOf, constraint⟩ = some edge := by
  let key : EdgeKey Symbol Constraint := ⟨symbol, children.map Value.referenceOf, constraint⟩
  obtain ⟨stored, present⟩ := keepFirst_present before.edgeRecords key
    (.mk (Cache.intern before.edges key).1 children)
  have recorded : (run (makeEdge symbol constraint children) before).2.edgeRecords key =
      some (run (makeEdge symbol constraint children) before).1 := by
    change (keepFirst before.edgeRecords key
      (.mk (Cache.intern before.edges key).1 children)) key =
        some (((keepFirst before.edgeRecords key
          (.mk (Cache.intern before.edges key).1 children)) key).getD
            (.mk (Cache.intern before.edges key).1 children))
    simp only [present, Option.getD_some]
  simpa only [observed] using recorded

private theorem makeEdge_heap_of_returned
    (symbol : Symbol) (constraint : Constraint) (children : List (Value Symbol Constraint))
    (before after : State Symbol Constraint) (edge : EdgeValue Symbol Constraint)
    (heap : Heap before) (coherent : Coherent after)
    (observed : run (makeEdge symbol constraint children) before = (edge, after))
    (checked : Fits edge.entry.key.constraint edge.children.length) : Heap after := by
  have recorded := makeEdge_record symbol constraint children before after edge observed
  have fields := (coherent.edges _ edge recorded).2
  have guardSame : edge.entry.key.constraint = constraint := congrArg EdgeKey.constraint fields.1
  have lengthSame : edge.children.length = children.length := by
    simpa only [List.length_map] using congrArg List.length fields.2
  have requested : Fits constraint children.length := by
    rw [← guardSame, ← lengthSame]
    exact checked
  have retained := SourcePruningEnumerationArityOrigins.edge_heap symbol constraint children before heap requested
  simpa only [observed] using retained

/-- The actual checked constructor preserves every old and newly stored edge-arity record. -/
theorem Receipt.preserves_arity_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {constraint : Allocated} {children : List (Value Symbol Constraint)}
    {before after : Checked width} {result : EdgeValue Symbol Constraint}
    (receipt : Receipt formulas solver inventory symbol constraint children before result after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  have checked : Fits result.entry.key.constraint result.children.length := by
    intro tries residual projected
    exact (receipt.projected_arity tries residual projected).2
  have coherent := receipt.ready.semantic.ready.semantic.1.normal.facts.coherent
  have actual := receipt.actual
  cases selected : (SourceEqualityMkEdgeAllocation.check constraint.stored constraint.guard children.length
      before.operations).1 with
  | error message =>
      simp only [build, SourceEqualityMkEdgeAllocation.build, selected] at actual
      cases actual
  | ok keep =>
      simp only [build, SourceEqualityMkEdgeAllocation.build, selected] at actual
      have resultSame := Except.ok.inj (congrArg Prod.fst actual)
      have heapSame := congrArg (fun returned => returned.2.native.machine.heap) actual
      change (run (SourceEqualityMkEdgeAllocation.work symbol (raw constraint) children keep)
        before.native.machine.heap).2 = after.native.machine.heap at heapSame
      have observed : run (SourceEqualityMkEdgeAllocation.work symbol (raw constraint) children keep)
          before.native.machine.heap = (result, after.native.machine.heap) :=
        Prod.ext resultSame heapSame
      cases keep with
      | false =>
          simp only [SourceEqualityMkEdgeAllocation.work, Bool.false_eq_true, ↓reduceIte] at observed
          exact makeEdge_heap_of_returned _ _ _ _ _ _ heap coherent observed checked
      | true =>
          simp only [SourceEqualityMkEdgeAllocation.work, ↓reduceIte] at observed
          exact makeEdge_heap_of_returned _ _ _ _ _ _ heap coherent observed checked

/-- Raw rejection preserves the entire edge-arity invariant without child availability. -/
theorem RejectReceipt.preserves_arity_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {before after : Checked width} {result : EdgeValue Symbol Constraint}
    (receipt : RejectReceipt formulas solver inventory symbol before result after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  have checked : Fits result.entry.key.constraint result.children.length := by
    intro tries residual projected
    exact (receipt.projected_arity tries residual projected).2
  have resultSame := congrArg Prod.fst receipt.actual
  have heapSame := congrArg (fun returned => returned.2.native.machine.heap) receipt.actual
  change (run (makeEdge symbol SourceEqualityConstraintConstructors.top [.empty])
    before.native.machine.heap).1 = result at resultSame
  change (run (makeEdge symbol SourceEqualityConstraintConstructors.top [.empty])
    before.native.machine.heap).2 = after.native.machine.heap at heapSame
  exact makeEdge_heap_of_returned _ _ _ _ _ _ heap
    receipt.ready.semantic.ready.semantic.1.normal.facts.coherent (Prod.ext resultSame heapSame) checked

end MicroCFTA.SourceCurrentAllocatedMkEdge
