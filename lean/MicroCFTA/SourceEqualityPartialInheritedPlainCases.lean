import MicroCFTA.SourceEqualityPartialInheritedPlainChildren

/-!
# Actual finite inherited rows and opaque caller branches

Every local empty-own pass derives its completed prefix and structural
children. Physical payload combination completes before recursive calls.
The actual child and edge effects supply the next row scope and histories.
-/
namespace MicroCFTA.SourceEqualityPartialInheritedPlainCases
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialInheritedPlainChildren
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Every inherited payload completes its ordered rows at each actual closed resident warm scope. -/
def RowsComplete (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ inherited (before : NativeState width Symbol Guard), Scope before → Edges before.machine.heap edges → ClosedEdges edges →
    ∃ results after, ReduceRows inherited edges before results after

/-- Actual cached probe reconstruction completes for every inherited payload at opaque Mu branches. -/
theorem binder (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard) :
    NodeComplete (width := width) (.mu entry body depth ordinary) := by
  intro _ before scope available _
  have clean := InternedFreshOrdinaryProbeHeap.resident before.machine.heap scope.probes entry body depth ordinary available
  have actual := SourceEqualityMuReconstruction.completed entry body depth ordinary before.machine.heap
    scope.native.semantic.ready.semantic.1.normal.facts.coherent available clean
  exact ⟨_, _, .binder actual⟩

/-- Actual inherited row completion supplies a finite ordinary source node through literal modifyNode. -/
theorem ordinary (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (ih : RowsComplete (width := width) edges) :
    NodeComplete (width := width) (.node entry edges depth free) := by
  intro inherited before scope available closed
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  obtain ⟨results, middle, trace⟩ := ih inherited before scope
    (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
    (SourceEqualityPartialStepProofs.closed_rows before scope.native entry edges depth free available closed)
  exact ⟨_, _, .ordinary trace⟩

/-- Complete actual empty-own prefixes, physical payloads, and smaller structural children derive every inherited row. -/
theorem rows_cons (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (edge : EdgeValue Symbol Guard) (edges : List (EdgeValue Symbol Guard))
    (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []))
    (childIH : ChildrenComplete (width := width) edge.children) (tailIH : RowsComplete (width := width) edges) :
    RowsComplete (width := width) (edge :: edges) := by
  intro inherited before scope resident closed
  have facts := scope.native.semantic.ready.semantic.1.normal.facts
  obtain ⟨narrowed, middle, native, own, shape⟩ := SourceEqualityPartialInheritedPlainPrefix.complete edge inherited before
    physical facts (resident _ List.mem_cons_self)
  have localPass := scope.narrow native (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) formulas solver ambient
  obtain ⟨payload, combined, _, _⟩ := @SourceEqualityInheritedPayload.combine_complete (Label FullSyntax.Formula) inherited (some [])
  obtain ⟨values, afterChildren, children⟩ := SourceEqualityPartialInheritedPlainChildren.complete childIH shape payload middle localPass.1
    (localPass.1.native.semantic.ready.semantic.1.normal.facts.cached.edges _ _ localPass.2.2.1) localPass.2.2.2.1
  have head := SourceEqualityPartialGraphLaws.edge_continuation formulas solver ambient own combined
    (SourceEqualityPartialGraphProofs.children formulas solver ambient children) localPass.1 localPass.2.2.1 localPass.2.2.2.1
  have kept := localPass.2.1.trans head.2.1
  obtain ⟨results, after, rest⟩ := tailIH inherited _ head.1
    (fun edge member => InternedEdgeResidency.edge_grows _ _ kept.growth edge (resident edge (List.mem_cons_of_mem _ member)))
    (fun edge member => closed edge (List.mem_cons_of_mem _ member))
  exact ⟨_, after, .cons native own combined children rest⟩

end MicroCFTA.SourceEqualityPartialInheritedPlainCases
