import MicroCFTA.SourceEqualityPartialMemoGraph

/-!
# Physical scopes for recursive source gate memo receipts

Actual native, child, and literal edge effects supply each later scope.
The existing public graph proofs give these effects at the exact completed
child receipt. No future heap or callback law is supplied.
-/
namespace MicroCFTA.SourceEqualityPartialMemoCases
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialMemoGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Node memo receipts use the actual initial physical scope and closed input. -/
def NodeMemos {inherited value result} {before after : NativeState width Symbol Guard}
    (trace : ReduceNode inherited value before result after) : Prop :=
  Scope before → Available before.machine.heap value → value.free = [] → NodeReads trace

/-- Row memo receipts use actual resident closed rows at the current warm state. -/
def RowsMemos {inherited edges results} {before after : NativeState width Symbol Guard}
    (trace : ReduceRows inherited edges before results after) : Prop :=
  Scope before → Edges before.machine.heap edges → ClosedEdges edges → RowsReads trace

/-- Child memo receipts require the actual closed available forest at its returned prefix state. -/
def ChildrenMemos {payload values results} {before after : NativeState width Symbol Guard}
    (trace : ReduceChildren payload values before results after) : Prop :=
  Scope before → Values before.machine.heap values → ClosedValues values → ChildrenReads trace

/-- Indexed walk memo receipts pass the actual scope through each completed child. -/
def WalkMemos {payload index values results} {before after : NativeState width Symbol Guard}
    (trace : WalkChildren payload index values before results after) : Prop :=
  Scope before → Values before.machine.heap values → ClosedValues values → WalkReads trace

/-- Actual node residency and closure supply every ordinary row memo premise. -/
theorem ordinary {inherited edges results entry depth free} {before middle : NativeState width Symbol Guard}
    {trace : ReduceRows inherited edges before results middle} (ih : RowsMemos trace) :
    NodeMemos (ReduceNode.ordinary (entry := entry) (depth := depth) (free := free) trace) := by
  intro scope available closed
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  exact .ordinary (ih scope (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
    (MergedColdReaderClosed.node_children_closed _ facts _ _ _ _ available closed))

/-- Each row derives native memo receipts and the real child and tail scopes from its actual effects. -/
theorem rows_cons (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    {edge narrowedEdge : EdgeValue Symbol Guard} {inherited own payload values edges results}
    {before middle afterChildren after : NativeState width Symbol Guard}
    (narrowed : SourceEqualityPCSNativeEdge.Execution edge inherited before narrowedEdge middle)
    (physical : SourceEqualityPhysicalPayload.own narrowedEdge.entry.key.constraint = .ok own)
    (combined : SourceEqualityInheritedPayload.combine inherited own = .ok payload)
    (children : ReduceChildren payload narrowedEdge.children middle values afterChildren)
    (rest : ReduceRows inherited edges
      (advanceHeap afterChildren (run (makeEdge narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values) afterChildren.machine.heap).2)
      results after)
    (childIH : ChildrenMemos children) (restIH : RowsMemos rest) :
    RowsMemos (.cons narrowed physical combined children rest) := by
  intro scope resident closed
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  have reads := SourceEqualityClosedMemoReads.edge narrowed facts (resident _ List.mem_cons_self) (closed _ List.mem_cons_self)
  have localPass := scope.narrow narrowed (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) formulas solver ambient
  have childReads := childIH localPass.1
    (localPass.1.native.semantic.ready.semantic.1.normal.facts.cached.edges _ _ localPass.2.2.1) localPass.2.2.2.1
  have head := SourceEqualityPartialGraphLaws.edge_continuation formulas solver ambient physical combined
    (SourceEqualityPartialGraphProofs.children formulas solver ambient children) localPass.1 localPass.2.2.1 localPass.2.2.2.1
  have kept := localPass.2.1.trans head.2.1
  have restReads := restIH head.1
    (fun edge member => InternedEdgeResidency.edge_grows _ _ kept.growth edge (resident edge (List.mem_cons_of_mem _ member)))
    (fun edge member => closed edge (List.mem_cons_of_mem _ member))
  exact .cons (physical := physical) (combined := combined) reads childReads restReads

/-- An actual successful child supplies the next scope and availability for its indexed tail. -/
theorem walk_cons (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    {payload index value result values results} {before middle after : NativeState width Symbol Guard}
    (head : ReduceNode (SourceEqualityDescend.descend payload index) value before result middle)
    (tail : WalkChildren payload (index + 1) values middle results after)
    (headIH : NodeMemos head) (tailIH : WalkMemos tail) : WalkMemos (.cons head tail) := by
  intro scope available closed
  have headReads := headIH scope (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
  have checked := SourceEqualityPartialGraphProofs.node formulas solver ambient head scope
    (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
  have restReads := tailIH checked.1
    (fun value member => checked.2.1.available value (available value (List.mem_cons_of_mem _ member)))
    (fun value member => closed value (List.mem_cons_of_mem _ member))
  exact .cons headReads restReads

end MicroCFTA.SourceEqualityPartialMemoCases
