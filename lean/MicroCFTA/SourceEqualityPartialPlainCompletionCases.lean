import MicroCFTA.SourceEqualityPartialPlainPrefix

/-!
# Finite actual caller branches for equality-free ordinary regions

Each smaller structural child call runs at the real returned warm state.
The local native prefix keeps the original structural child list. Actual
graph effects supply the next child and row scopes. No complete caller
graph or general recursive termination law is an input premise.
-/
namespace MicroCFTA.SourceEqualityPartialPlainCompletionCases
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialScope SourceEqualityPartialGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Every closed available input completes at its actual initial warm scope. -/
def NodeComplete (value : Value Symbol Guard) : Prop :=
  ∀ before : NativeState width Symbol Guard, Scope before → Available before.machine.heap value → value.free = [] →
    ∃ result after, ReduceNode (some []) value before result after

/-- Ordered actual rows complete at every closed resident warm scope. -/
def RowsComplete (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ before : NativeState width Symbol Guard, Scope before → Edges before.machine.heap edges → ClosedEdges edges →
    ∃ results after, ReduceRows (some []) edges before results after

/-- The actual indexed child walk completes from any child position and closed available scope. -/
def ChildrenComplete (values : List (Value Symbol Guard)) : Prop :=
  ∀ index (before : NativeState width Symbol Guard), Scope before → Values before.machine.heap values → ClosedValues values →
    ∃ results after, WalkChildren (some []) index values before results after

/-- Available Mu records complete through the actual fixed probes and resident canonical hit. -/
theorem binder (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard) :
    NodeComplete (width := width) (.mu entry body depth ordinary) := by
  intro before scope available _
  have clean := InternedFreshOrdinaryProbeHeap.resident before.machine.heap scope.probes entry body depth ordinary available
  have actual := SourceEqualityMuReconstruction.completed entry body depth ordinary before.machine.heap
    scope.native.semantic.ready.semantic.1.normal.facts.coherent available clean
  exact ⟨_, _, .binder actual⟩

/-- Actual resident ordinary rows supply a finite completed node through literal modifyNode. -/
theorem ordinary (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (ih : RowsComplete (width := width) edges) :
    NodeComplete (width := width) (.node entry edges depth free) := by
  intro before scope available closed
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  obtain ⟨results, middle, trace⟩ := ih before scope
    (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
    (SourceEqualityPartialStepProofs.closed_rows before scope.native entry edges depth free available closed)
  exact ⟨_, _, .ordinary trace⟩

/-- A completed smaller child derives the actual scope and availability used by the indexed tail. -/
theorem children_cons (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (value : Value Symbol Guard) (values : List (Value Symbol Guard))
    (headIH : NodeComplete (width := width) value) (tailIH : ChildrenComplete (width := width) values) :
    ChildrenComplete (width := width) (value :: values) := by
  intro index before scope available closed
  obtain ⟨result, middle, first⟩ := headIH before scope (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
  have checked := SourceEqualityPartialGraphProofs.node formulas solver ambient first scope
    (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
  obtain ⟨results, after, rest⟩ := tailIH (index + 1) middle checked.1
    (fun value member => checked.2.1.available value (available value (List.mem_cons_of_mem _ member)))
    (fun value member => closed value (List.mem_cons_of_mem _ member))
  exact ⟨result :: results, after, .cons first rest⟩

/-- Actual empty native prefixes and structural child completion derive finite ordered row completion. -/
theorem rows_cons (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (edge : EdgeValue Symbol Guard) (edges : List (EdgeValue Symbol Guard))
    (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []))
    (childIH : ChildrenComplete (width := width) edge.children) (tailIH : RowsComplete (width := width) edges) :
    RowsComplete (width := width) (edge :: edges) := by
  intro before scope resident closed
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  have native := SourceEqualityPartialPlainPrefix.execute edge before physical
  have fields := SourceEqualityPartialPlainPrefix.fields edge before facts (resident _ List.mem_cons_self) physical
  have localPass := scope.narrow native (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) formulas solver ambient
  have narrowedAvailable := localPass.1.native.semantic.ready.semantic.1.normal.facts.cached.edges _ _ localPass.2.2.1
  obtain ⟨values, afterChildren, walked⟩ := childIH 0 _ localPass.1
    (by intro child member; exact narrowedAvailable child (by simpa only [fields.2] using member))
    (by simpa only [fields.2] using localPass.2.2.2.1)
  have children : ReduceChildren (some [])
      (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint edge.children) before.machine.heap).1.children
      (advanceHeap before (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint edge.children) before.machine.heap).2)
      values afterChildren := .live (by simpa only [fields.2] using walked)
  have head := SourceEqualityPartialGraphLaws.edge_continuation formulas solver ambient fields.1
    SourceEqualityPartialPlainPrefix.combine_empty (SourceEqualityPartialGraphProofs.children formulas solver ambient children)
    localPass.1 localPass.2.2.1 localPass.2.2.2.1
  have kept := localPass.2.1.trans head.2.1
  obtain ⟨results, after, rest⟩ := tailIH _ head.1
    (fun edge member => InternedEdgeResidency.edge_grows _ _ kept.growth edge (resident edge (List.mem_cons_of_mem _ member)))
    (fun edge member => closed edge (List.mem_cons_of_mem _ member))
  exact ⟨_, after, .cons native fields.1 SourceEqualityPartialPlainPrefix.combine_empty children rest⟩

end MicroCFTA.SourceEqualityPartialPlainCompletionCases
