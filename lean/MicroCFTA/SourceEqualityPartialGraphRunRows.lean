import MicroCFTA.SourceEqualityPartialGraphRuns

/-!
# Actual row execution with changing bounded recursive callbacks

The native prefix has its own stable stage bounds. Actual child and tail
graphs reproduce their full returned states at larger traversal bounds.
Their common maximum therefore replays the complete source row schedule.
-/
namespace MicroCFTA.SourceEqualityPartialGraphRuns
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A complete source row replays its native prefix, payload calls, actual recursive children, and ordered tail. -/
theorem rows_cons {edge narrowedEdge : EdgeValue Symbol Guard} {inherited own payload values edges results}
    {before middle afterChildren after : NativeState width Symbol Guard}
    (narrowed : SourceEqualityPCSNativeEdge.Execution edge inherited before narrowedEdge middle)
    (physical : SourceEqualityPhysicalPayload.own narrowedEdge.entry.key.constraint = .ok own)
    (combined : SourceEqualityInheritedPayload.combine inherited own = .ok payload)
    (childrenIH : ChildrenRun payload narrowedEdge.children middle values afterChildren)
    (restIH : RowsRun inherited edges
      (advanceHeap afterChildren (run (makeEdge narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values) afterChildren.machine.heap).2) results after) :
    RowsRun inherited (edge :: edges) before
      ((run (makeEdge narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values) afterChildren.machine.heap).1 :: results) after := by
  obtain ⟨bg, be, bp, bh, bc, bn, native⟩ := SourceEqualityGuardedEdgeWorkerProofs.stable source top conjoin SourceMemoGate.plain top narrowed
  obtain ⟨childBound, children⟩ := childrenIH
  obtain ⟨tailBound, tail⟩ := restIH
  refine ⟨max (max bg (max be (max bp (max bh (max bc bn))))) (max childBound tailBound), ?_⟩
  intro g e p h c n fuel enoughG enoughE enoughP enoughH enoughC enoughN enoughFuel
  have localDone := native g e p h c n (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have childDone := children g e p h c n fuel (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have tailDone := tail g e p h c n fuel (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [SourceEqualityInheritedRows.walk, SourceEqualityInheritedEdgeWorker.run, localDone,
    SourceEqualityInheritedEdgeWorker.descendants, physical, combined, childDone, tailDone]

end MicroCFTA.SourceEqualityPartialGraphRuns
