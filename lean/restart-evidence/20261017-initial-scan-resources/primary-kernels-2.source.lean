import MicroCFTA.SourceCurrentPrimaryGateNumericReplay

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.PrimaryNumericIntegration
open InternedConstructorTemplates InternedNestedConstruction
private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 true [.binder false (.node [.mk 1 true [.var 0, .var 1]])]])
private def outcome := InternedFreshOrdinaryConstruction.build expression [] empty
private def before := outcome.state
private def original : Value Nat Bool := match outcome with | .done value _ => value | .pending _ _ => .empty
private def body : Value Nat Bool := match original with
  | .mu _ value _ _ => value
  | _ => .empty
private def selected : Value Nat Bool := match original with
  | .mu _ (.node _ [.mk _ [child]] _ _) _ _ => child
  | _ => .empty
#eval (before.nodes.next, before.edges.next, original.free.isEmpty, selected.free.isEmpty)
private theorem built : InternedFreshOrdinaryConstruction.build expression [] empty = .done original before := by cbv
private theorem selected_available : InternedProbeProvenance.Available before selected := by
  have originalAvailable := (InternedFreshOrdinaryFacts.closed_verified expression).result original before built
  have bodyAvailable := originalAvailable.children body (by cbv; exact List.mem_cons_self)
  exact bodyAvailable.children selected (by cbv; exact List.mem_cons_self)
private def values : List (Value Nat Bool) := [selected, .reference .depth]
private def paths : List (List Nat) := [[9], [0], [1]]
private def call := EndpointStatefulGate.classMeets (fun _ => true) (fun _ => false) 4 values paths before
private def after := call.state
#eval (after.nodes.next, after.edges.next)
private theorem cold : EndpointStatefulGate.classMeets (fun _ => true) (fun _ => false) 4 values paths before = .done (some true) after := by cbv
private theorem warm : EndpointStatefulGate.classMeets (fun _ => true) (fun _ => false) 4 values paths after = .done (some true) after := by cbv
private theorem allocated : before.nodes.next < after.nodes.next ∧ before.edges.next < after.edges.next := by cbv

private def initialBound : Nat := SourceCurrentMemoMergeResourceControl.initialBound before.nodes.next before.edges.next (InternedValueMassHeap.initialBound before)
private theorem initial_values : InternedNestedProvenance.Values before values := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact selected_available
  · have same := List.mem_singleton.mp member
    subst value
    exact InternedProbeProvenance.reference_available before .depth (by intro identity impossible; simp [Value.free] at impossible)

/-- An own nested source gives an allocating open-Mu primary call at its initial numeric forecast. -/
theorem initial_allocating_primary :
    ¬ MergedColdReaderClosedInputs.ClosedValues values ∧
    SourceEqualityRequiredSemanticCache.SemanticReady after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧
    InternedNestedProvenance.Values after values ∧
    SourceCurrentMemoMergeResourceControl.Fits (SourceCurrentPrimaryGateResources.classBound paths initialBound) after ∧
    before.nodes.next < after.nodes.next ∧ before.edges.next < after.edges.next ∧
    ∀ fuel, SourceCurrentPrimaryGateResources.classFuel paths initialBound ≤ fuel →
      EndpointStatefulGate.classMeets (fun _ => true) (fun _ => false) fuel values paths before = .done (some true) after := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression original before built
  have costs : InternedFreshOrdinaryCostHeap.Heap before := by
    simpa only [built, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  have stored := InternedValueMassHeap.initial before semantic.ready.semantic.1.normal.facts
  have fits := SourceCurrentMemoMergeResourceControl.initial before _ stored
  obtain ⟨answer, heap, graph, returned, returnedCosts, kept, retained, finalFits, stable⟩ :=
    SourceCurrentPrimaryGateNumericReplay.class_complete (fun _ => true) (fun _ => false)
      values paths before semantic costs initial_values initialBound fits
  have small := EndpointStatefulGateTrace.class_trace_of_done (fun _ => true) (fun _ => false)
    4 values paths before true after cold
  obtain ⟨rfl, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique _ _ _ _ _ _ _ _ _ graph small
  refine ⟨?_, returned, returnedCosts, retained, finalFits, allocated.1, allocated.2, stable⟩
  intro closed
  have impossible := closed (.reference .depth) (by exact List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [Value.free, List.cons_ne_self] at impossible

/-- The first produced full heap is a new initial input for an exact allocation-free warm call. -/
theorem warm_at_first_return :
    SourceCurrentMemoMergeResourceControl.Fits
      (SourceCurrentPrimaryGateResources.classBound paths (SourceCurrentPrimaryGateResources.classBound paths initialBound)) after ∧
    ∀ fuel, SourceCurrentPrimaryGateResources.classFuel paths
        (SourceCurrentPrimaryGateResources.classBound paths initialBound) ≤ fuel →
      EndpointStatefulGate.classMeets (fun _ => true) (fun _ => false) fuel values paths after = .done (some true) after := by
  obtain ⟨_, semantic, costs, available, fits, _, _, _⟩ := initial_allocating_primary
  obtain ⟨answer, heap, graph, _, _, _, _, finalFits, stable⟩ :=
    SourceCurrentPrimaryGateNumericReplay.class_complete (fun _ => true) (fun _ => false)
      values paths after semantic costs available _ fits
  have small := EndpointStatefulGateTrace.class_trace_of_done (fun _ => true) (fun _ => false)
    4 values paths after true after warm
  obtain ⟨rfl, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique _ _ _ _ _ _ _ _ _ graph small
  exact ⟨finalFits, stable⟩

end MicroCFTA.PrimaryNumericIntegration
#print axioms MicroCFTA.PrimaryNumericIntegration.initial_allocating_primary
#check @MicroCFTA.PrimaryNumericIntegration.initial_allocating_primary
#print axioms MicroCFTA.PrimaryNumericIntegration.warm_at_first_return
#check @MicroCFTA.PrimaryNumericIntegration.warm_at_first_return
