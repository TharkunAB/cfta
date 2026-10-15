import MicroCFTA.SourceEqualityClosedMemoReads

/-!
# Both source gate memo receipts in complete recursive reduction graphs

These predicates index the existing complete graphs. Each row retains the
actual closed native prefix receipt, then the actual child and tail memo
receipts. They add no language law or recursive callback premise.
-/
namespace MicroCFTA.SourceEqualityPartialMemoGraph
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityPartialGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

mutual
/-- A node retains every source gate memo call in its actual recursive rows. -/
inductive NodeReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {inherited : SourceEqualityPrecheck.Constraint} → {value : Value Symbol Guard} → {before : NativeState width Symbol Guard} →
    {result : Value Symbol Guard} → {after : NativeState width Symbol Guard} → ReduceNode inherited value before result after → Prop where
  | empty : NodeReads .empty
  | union : NodeReads .union
  | binder {before : NativeState width Symbol Guard}
      (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.machine.heap = .done result heap) :
      NodeReads (.binder actual)
  | ordinary (rows : RowsReads trace) : NodeReads (.ordinary trace)

/-- Ordered rows retain both actual memo tables at every local native prefix and recursive continuation. -/
inductive RowsReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {inherited : SourceEqualityPrecheck.Constraint} → {edges : List (EdgeValue Symbol Guard)} → {before : NativeState width Symbol Guard} →
    {results : List (EdgeValue Symbol Guard)} → {after : NativeState width Symbol Guard} → ReduceRows inherited edges before results after → Prop where
  | nil : RowsReads .nil
  | cons {narrowed : SourceEqualityPCSNativeEdge.Execution edge inherited before narrowedEdge middle}
      {physical : SourceEqualityPhysicalPayload.own narrowedEdge.entry.key.constraint = .ok own}
      {combined : SourceEqualityInheritedPayload.combine inherited own = .ok payload}
      {children : ReduceChildren payload narrowedEdge.children middle values afterChildren}
      {rest : ReduceRows inherited edges
        (advanceHeap afterChildren (run (makeEdge narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values) afterChildren.machine.heap).2)
        results after}
      (reads : SourceEqualityClosedMemoReads.EdgeReads narrowed) (childReads : ChildrenReads children) (restReads : RowsReads rest) :
      RowsReads (.cons narrowed physical combined children rest)

/-- Child memo receipts retain the actual contradiction or live traversal branch. -/
inductive ChildrenReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {payload : SourceEqualityPrecheck.Constraint} → {values : List (Value Symbol Guard)} → {before : NativeState width Symbol Guard} →
    {results : List (Value Symbol Guard)} → {after : NativeState width Symbol Guard} → ReduceChildren payload values before results after → Prop where
  | contradiction : ChildrenReads .contradiction
  | live (reads : WalkReads trace) : ChildrenReads (.live trace)

/-- Each actual indexed child and returned tail retains its own source gate memo receipts. -/
inductive WalkReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {payload : SourceEqualityPrecheck.Constraint} → {index : Nat} → {values : List (Value Symbol Guard)} → {before : NativeState width Symbol Guard} →
    {results : List (Value Symbol Guard)} → {after : NativeState width Symbol Guard} → WalkChildren payload index values before results after → Prop where
  | nil : WalkReads .nil
  | cons (first : NodeReads head) (rest : WalkReads tail) : WalkReads (.cons head tail)
end

end MicroCFTA.SourceEqualityPartialMemoGraph
