import MicroCFTA.SourceEqualityPartialProbeEntry

/-!
# Mutually recursive completed source partial-reduction graphs

Each child reduction carries its own actual node graph. Rows retain the
checked native prefix, physical payload calls, ordered children, literal
edge construction, and actual next warm state. No recursive callback law
is a graph premise. This graph describes successful finite executions.
-/
namespace MicroCFTA.SourceEqualityPartialGraph
open Cache InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

mutual
/-- A completed outer node uses actual source branches and recursive row evidence. -/
inductive ReduceNode [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      Value Symbol Guard → NativeState width Symbol Guard → Prop where
  | empty : ReduceNode inherited .empty before .empty before
  | union : ReduceNode inherited (.union entry members depth free) before (.union entry members depth free) before
  | binder (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.machine.heap = .done result heap) :
      ReduceNode inherited (.mu entry body depth ordinary) before result (advanceHeap before heap)
  | ordinary (rows : ReduceRows inherited edges before results middle) :
      ReduceNode inherited (.node entry edges depth free) before
        (SourceEqualityPartialNodeRebuild.modify (.node entry edges depth free) edges results middle).1
        (SourceEqualityPartialNodeRebuild.modify (.node entry edges depth free) edges results middle).2

/-- Ordered rows retain their exact native pass and inherited child continuation before the tail. -/
inductive ReduceRows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    SourceEqualityPrecheck.Constraint → List (EdgeValue Symbol Guard) → NativeState width Symbol Guard →
      List (EdgeValue Symbol Guard) → NativeState width Symbol Guard → Prop where
  | nil : ReduceRows inherited [] before [] before
  | cons (narrowed : SourceEqualityPCSNativeEdge.Execution edge inherited before narrowedEdge middle)
      (physical : SourceEqualityPhysicalPayload.own narrowedEdge.entry.key.constraint = .ok own)
      (combined : SourceEqualityInheritedPayload.combine inherited own = .ok payload)
      (children : ReduceChildren payload narrowedEdge.children middle values afterChildren)
      (rest : ReduceRows inherited edges
        (advanceHeap afterChildren (run (makeEdge narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values) afterChildren.machine.heap).2)
        results after) :
      ReduceRows inherited (edge :: edges) before
        ((run (makeEdge narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values) afterChildren.machine.heap).1 :: results) after

/-- Actual contradiction maps EmptyNode; live payloads start the source walk at child index zero. -/
inductive ReduceChildren [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    SourceEqualityPrecheck.Constraint → List (Value Symbol Guard) → NativeState width Symbol Guard →
      List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
  | contradiction : ReduceChildren none values before (values.map (fun _ => .empty)) before
  | live (walk : WalkChildren (some records) 0 values before results after) :
      ReduceChildren (some records) values before results after

/-- Every selected child carries its real descended constraints, node graph, and next warm state. -/
inductive WalkChildren [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    SourceEqualityPrecheck.Constraint → Nat → List (Value Symbol Guard) → NativeState width Symbol Guard →
      List (Value Symbol Guard) → NativeState width Symbol Guard → Prop where
  | nil : WalkChildren inherited index [] before [] before
  | cons (first : ReduceNode (SourceEqualityDescend.descend inherited index) value before result middle)
      (rest : WalkChildren inherited (index + 1) values middle results after) :
      WalkChildren inherited index (value :: values) before (result :: results) after
end

end MicroCFTA.SourceEqualityPartialGraph
