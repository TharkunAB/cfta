import MicroCFTA.SourceEqualityConstraintPassClosure
import MicroCFTA.SourceEqualityPartialMemoProofs

/-!
# Constraint closure through actual outer recursive reduction

Mutual graph induction passes the constraint heap through actual narrowed
prefixes, descended child calls, literal edge requests, and row tails.
Resident Mu reconstruction leaves the constructor heap unchanged. Both
modifyNode branches preserve the returned row heap. This theorem describes
completed graphs. It does not assert that every caller terminates.
-/
namespace MicroCFTA.SourceEqualityPartialConstraintClosure
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialScope SourceEqualityPartialGraph
open SourceEqualityAnnotationHeap (Heap)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A completed node carries its constraint heap from its actual closed input scope. -/
def NodeHeap (annotation : Guard → Prop) {inherited value result} {before after : NativeState width Symbol Guard}
    (_trace : ReduceNode inherited value before result after) : Prop :=
  Scope before → Available before.machine.heap value → value.free = [] →
    Heap annotation before.machine.heap → Heap annotation after.machine.heap

/-- Ordered rows carry annotations through their actual native prefix and child continuations. -/
def RowsHeap (annotation : Guard → Prop) {inherited edges results} {before after : NativeState width Symbol Guard}
    (_trace : ReduceRows inherited edges before results after) : Prop :=
  Scope before → Edges before.machine.heap edges → ClosedEdges edges →
    Heap annotation before.machine.heap → Heap annotation after.machine.heap

/-- Child execution carries annotations at its actual returned native prefix state. -/
def ChildrenHeap (annotation : Guard → Prop) {payload values results} {before after : NativeState width Symbol Guard}
    (_trace : ReduceChildren payload values before results after) : Prop :=
  Scope before → Values before.machine.heap values → ClosedValues values →
    Heap annotation before.machine.heap → Heap annotation after.machine.heap

/-- Each indexed walk uses the heap returned by its completed head. -/
def WalkHeap (annotation : Guard → Prop) {payload index values results} {before after : NativeState width Symbol Guard}
    (_trace : WalkChildren payload index values before results after) : Prop :=
  Scope before → Values before.machine.heap values → ClosedValues values →
    Heap annotation before.machine.heap → Heap annotation after.machine.heap

/-- Physical cached probes derive the unchanged heap of actual Mu reconstruction. -/
theorem binder (annotation : Guard → Prop) {entry body depth ordinary result heap inherited}
    {before : NativeState width Symbol Guard}
    (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.machine.heap = .done result heap) :
    NodeHeap annotation (.binder (inherited := inherited) actual) := by
  intro scope available _ origins
  have clean := InternedFreshOrdinaryProbeHeap.resident before.machine.heap scope.probes entry body depth ordinary available
  have checked := SourceEqualityMuReconstruction.completed entry body depth ordinary before.machine.heap
    scope.native.semantic.ready.semantic.1.normal.facts.coherent available clean
  have parts := InternedNestedConstruction.Outcome.done.inj (checked.symm.trans actual)
  cases parts.1
  cases parts.2
  exact origins

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (ambient : InternedGuardedLanguage.Env Symbol)
include formulas solver ambient

/-- Actual row effects supply both modifyNode branches with the returned constraint heap. -/
theorem ordinary (annotation : Guard → Prop) {inherited edges results entry depth free}
    {before middle : NativeState width Symbol Guard} {trace : ReduceRows inherited edges before results middle}
    (ih : RowsHeap annotation trace) :
    NodeHeap annotation (ReduceNode.ordinary (entry := entry) (depth := depth) (free := free) trace) := by
  intro scope available closed origins
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
  have rowClosed := SourceEqualityPartialStepProofs.closed_rows before scope.native entry edges depth free available closed
  have rows := SourceEqualityPartialGraphProofs.rows formulas solver ambient trace scope resident rowClosed
  have built := SourceEqualityPartialNodeRebuild.verified annotation top conjoin entry edges results depth free middle
    rows.1.native (rows.2.1.available _ available) closed rows.2.2.1 rows.2.2.2.1
    (ih scope resident rowClosed origins) (acceptsConstraint formulas solver) ambient
  exact built.2.2.2.2.1

/-- Real narrowing, child execution, literal interning, and the tail derive the final constraint heap. -/
theorem rows_cons (annotation : Guard → Prop) (topValid : annotation top)
    (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    {edge narrowedEdge : EdgeValue Symbol Guard} {inherited own payload values edges results}
    {before middle afterChildren after : NativeState width Symbol Guard}
    (narrowed : SourceEqualityPCSNativeEdge.Execution edge inherited before narrowedEdge middle)
    (physical : SourceEqualityPhysicalPayload.own narrowedEdge.entry.key.constraint = .ok own)
    (combined : SourceEqualityInheritedPayload.combine inherited own = .ok payload)
    (children : ReduceChildren payload narrowedEdge.children middle values afterChildren)
    (rest : ReduceRows inherited edges
      (advanceHeap afterChildren (run (makeEdge narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values) afterChildren.machine.heap).2)
      results after)
    (childIH : ChildrenHeap annotation children) (restIH : RowsHeap annotation rest) :
    RowsHeap annotation (.cons narrowed physical combined children rest) := by
  intro scope resident closed origins
  have localPass := scope.narrow narrowed (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) formulas solver ambient
  have localHeap := SourceEqualityConstraintPassClosure.guarded_edge_heap annotation topValid conjoinedValid topValid
    narrowed scope.native (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) origins
  have childHeap := childIH localPass.1
    (localPass.1.native.semantic.ready.semantic.1.normal.facts.cached.edges _ _ localPass.2.2.1) localPass.2.2.2.1 localHeap
  have head := SourceEqualityPartialGraphLaws.edge_continuation formulas solver ambient physical combined
    (SourceEqualityPartialGraphProofs.children formulas solver ambient children) localPass.1 localPass.2.2.1 localPass.2.2.2.1
  have builtHeap := SourceEqualityAnnotationHeap.run annotation _
    (SourceEqualityAnnotationHeap.makeEdge annotation narrowedEdge.entry.key.symbol narrowedEdge.entry.key.constraint values
      (localHeap _ _ localPass.2.2.1)) afterChildren.machine.heap childHeap
  have kept := localPass.2.1.trans head.2.1
  exact restIH head.1
    (fun edge member => InternedEdgeResidency.edge_grows _ _ kept.growth edge (resident edge (List.mem_cons_of_mem _ member)))
    (fun edge member => closed edge (List.mem_cons_of_mem _ member)) builtHeap

/-- The actual completed head derives the scope and annotations used by the remaining indexed children. -/
theorem walk_cons (annotation : Guard → Prop) {payload index value result values results}
    {before middle after : NativeState width Symbol Guard}
    (head : ReduceNode (SourceEqualityDescend.descend payload index) value before result middle)
    (tail : WalkChildren payload (index + 1) values middle results after)
    (headIH : NodeHeap annotation head) (tailIH : WalkHeap annotation tail) :
    WalkHeap annotation (.cons head tail) := by
  intro scope available closed origins
  have nextHeap := headIH scope (available _ List.mem_cons_self) (closed _ List.mem_cons_self) origins
  have checked := SourceEqualityPartialGraphProofs.node formulas solver ambient head scope
    (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
  exact tailIH checked.1
    (fun value member => checked.2.1.available value (available value (List.mem_cons_of_mem _ member)))
    (fun value member => closed value (List.mem_cons_of_mem _ member)) nextHeap

/-- Mutual induction derives constraint closure at every actual outer recursive return. -/
theorem node (annotation : Guard → Prop) (topValid : annotation top)
    (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    {inherited value result} {before after : NativeState width Symbol Guard}
    (trace : ReduceNode inherited value before result after) : NodeHeap annotation trace := by
  exact ReduceNode.rec
    (motive_1 := fun _ _ _ _ _ trace => NodeHeap annotation trace)
    (motive_2 := fun _ _ _ _ _ trace => RowsHeap annotation trace)
    (motive_3 := fun _ _ _ _ _ trace => ChildrenHeap annotation trace)
    (motive_4 := fun _ _ _ _ _ _ trace => WalkHeap annotation trace)
    (fun {_ _} _ _ _ heap => heap)
    (fun {_ _ _ _ _ _} _ _ _ heap => heap)
    (fun {_ _ _ _ _ _ _ _} actual => binder annotation actual)
    (fun {_ _ _ _ _ _ _ _} _ ih => ordinary formulas solver ambient annotation ih)
    (fun {_ _} _ _ _ heap => heap)
    (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined children rest childIH restIH =>
      rows_cons formulas solver ambient annotation topValid conjoinedValid narrowed physical combined children rest childIH restIH)
    (fun {_ _} _ _ _ heap => heap)
    (fun {_ _ _ _ _} _ ih scope available closed heap => ih scope available closed heap)
    (fun {_ _ _} _ _ _ heap => heap)
    (fun {_ _ _ _ _ _ _ _ _} head tail headIH tailIH =>
      walk_cons formulas solver ambient annotation head tail headIH tailIH) trace

/-- Actual checked bounded success derives constraint closure without a supplied caller graph. -/
theorem checked (annotation : Guard → Prop) (topValid : annotation top)
    (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    (g e p h c n fuel : Nat) {inherited value result} {before after : NativeState width Symbol Guard}
    (plan : SourceEqualityPartialChecks.Checked g e p h c n fuel inherited value before)
    (done : SourceEqualityPartialWorker.run g e p h c n fuel inherited value before = .done (.ok result) after)
    (scope : Scope before) (available : Available before.machine.heap value) (closed : value.free = [])
    (heap : Heap annotation before.machine.heap) : Heap annotation after.machine.heap :=
  node formulas solver ambient annotation topValid conjoinedValid
    (SourceEqualityPartialWorkerGraph.graph g e p h c n fuel plan done) scope available closed heap

end MicroCFTA.SourceEqualityPartialConstraintClosure
