import MicroCFTA.SourceEqualityInheritedEdge

/-!
# Bounded local edge worker with actual inherited descendants

The source guarded-edge stage completes before inherited child processing.
Both stages retain their exact errors and incomplete observations. Successful
workers and complete edge graphs agree in both directions. Six native stage
bounds remain local; the recursive node callback is fixed in this worker.
-/
namespace MicroCFTA.SourceEqualityInheritedEdgeWorker
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityInheritedEdge
universe u
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained

/-- Each edge observation retains its actual completed scope or unfinished source stage. -/
inductive Result (width : Nat) (Observation : Type u) : Type (max 1 u) where
  | done (answer : Except String (EdgeValue Symbol Guard)) (state : NativeState width Symbol Guard)
  | guarded (observation : SourceEqualityGuardedEdgeWorker.Result width FullSyntax.Formula)
  | children (observation : Observation)

/-- Execute the actual inherited/local payload combination, indexed children, and original-label constructor. -/
noncomputable def descendants [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation)
    (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) : Result width Observation :=
  match SourceEqualityPhysicalPayload.own edge.entry.key.constraint with
  | .error message => .done (.error message) before
  | .ok own => match SourceEqualityInheritedPayload.combine inherited own with
    | .error message => .done (.error message) before
    | .ok payload => match SourceEqualityInheritedChildren.run call payload edge.children before with
      | .incomplete observation => .children observation
      | .done (.error message) middle => .done (.error message) middle
      | .done (.ok values) middle =>
          let built := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap
          .done (.ok built.1) (advanceHeap middle built.2)

/-- Run concrete source local narrowing before the inherited descendant continuation. -/
noncomputable def run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard →
      SourceEqualityInheritedChildren.Result width Symbol Guard (Value Symbol Guard) Observation)
    (g e p h c n : Nat) (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) : Result width Observation :=
  match SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top g e p h c n edge inherited before with
  | .done (.ok narrowed) middle => descendants call narrowed inherited middle
  | .done (.error message) middle => .done (.error message) middle
  | observation => .guarded observation

/-- Each complete inherited continuation executes at its identical physical edge and full native state. -/
theorem graph_executes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call edge inherited before result after} (trace : Graph (Observation := Observation) (width := width) call edge inherited before result after) :
    descendants call edge inherited before = .done (.ok result) after := by
  cases trace with
  | done physical combined children =>
      simp only [descendants, physical, combined, SourceEqualityInheritedChildren.execution_iff.mp children]

/-- Successful inherited continuation execution derives all literal source graph receipts. -/
theorem descendants_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call edge inherited before result after}
    (done : descendants (Observation := Observation) (width := width) call edge inherited before = .done (.ok result) after) :
    Graph call edge inherited before result after := by
  cases physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint with
  | error => simp only [descendants, physical] at done; cases done
  | ok own =>
      cases combined : SourceEqualityInheritedPayload.combine inherited own with
      | error => simp only [descendants, physical, combined] at done; cases done
      | ok payload =>
          cases actual : SourceEqualityInheritedChildren.run call payload edge.children before with
          | incomplete => simp only [descendants, physical, combined, actual] at done; cases done
          | done answer middle =>
              cases answer with
              | error => simp only [descendants, physical, combined, actual] at done; cases done
              | ok values =>
                  simp only [descendants, physical, combined, actual] at done
                  have parts := Result.done.inj done
                  have same := Except.ok.inj parts.1
                  cases same; cases parts.2
                  exact .done physical combined (SourceEqualityInheritedChildren.execution_iff.mpr actual)

/-- Complete local edge processing has stable identical results at all sufficient native stage bounds for its fixed node callback. -/
theorem stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call edge inherited before result after} (trace : Execution (Observation := Observation) (width := width) call edge inherited before result after) :
    ∃ g e p h c n, ∀ gg ee pp hh cc nn, g ≤ gg → e ≤ ee → p ≤ pp → h ≤ hh → c ≤ cc → n ≤ nn →
      run call gg ee pp hh cc nn edge inherited before = .done (.ok result) after := by
  cases trace with
  | done narrowed children =>
      obtain ⟨g, e, p, h, c, n, actual⟩ := SourceEqualityGuardedEdgeWorkerProofs.stable source top conjoin SourceMemoGate.plain top narrowed
      refine ⟨g, e, p, h, c, n, ?_⟩
      intro gg ee pp hh cc nn enoughG enoughE enoughP enoughH enoughC enoughN
      simp only [run, actual gg ee pp hh cc nn enoughG enoughE enoughP enoughH enoughC enoughN, graph_executes children]

/-- Every successful bounded full edge worker gives its actual concrete narrowing and inherited continuation graphs. -/
theorem run_graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call edge inherited before result after} (g e p h c n : Nat)
    (ranges : SourceEqualityPCSNativeEdge.Ranges edge inherited before)
    (done : run (Observation := Observation) (width := width) call g e p h c n edge inherited before = .done (.ok result) after) :
    Execution call edge inherited before result after := by
  cases actual : SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top g e p h c n edge inherited before with
  | children => simp only [run, actual] at done; cases done
  | done answer middle =>
      cases answer with
      | error => simp only [run, actual] at done; cases done
      | ok narrowed =>
          have first := SourceEqualityGuardedEdgeWorkerProofs.graph source top conjoin SourceMemoGate.plain top g e p h c n edge inherited before ranges narrowed middle actual
          exact .done first (descendants_graph (by simpa only [run, actual] using done))

/-- Complete full edge graphs and successful bounded execution agree in both directions. -/
theorem execution_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {call edge inherited before result after} (ranges : SourceEqualityPCSNativeEdge.Ranges edge inherited before) :
    Execution (Observation := Observation) (width := width) call edge inherited before result after ↔
      ∃ g e p h c n, run call g e p h c n edge inherited before = .done (.ok result) after := by
  constructor
  · intro trace
    obtain ⟨g, e, p, h, c, n, actual⟩ := stable trace
    exact ⟨g, e, p, h, c, n, actual g e p h c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨g, e, p, h, c, n, done⟩
    exact run_graph g e p h c n ranges done

end MicroCFTA.SourceEqualityInheritedEdgeWorker
