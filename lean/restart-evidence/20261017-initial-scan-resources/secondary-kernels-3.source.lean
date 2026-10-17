import MicroCFTA.SourceCurrentSecondaryGateResources
import MicroCFTA.InternedFreshOrdinaryStoredCosts
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.SecondaryNumericKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentSecondaryGateResources
open SourceCurrentSecondaryTrace
open SourceCurrentPrimaryGateResources

private def expression : Syntax Nat Bool :=
  .binder false (.binder false (.node [.mk 0 false [.var 0, .var 1], .mk 1 true []]))
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def source := built.state
private def inner : Value Nat Bool := match original with | .mu _ body _ _ => body | _ => .empty
private def unfolded := InternedFreshOrdinaryStoredSubstitution.unfold inner source
private def exposed : Value Nat Bool := match unfolded with | .done value _ => value | .pending .. => .empty
private def heap := unfolded.state
private def scalar := SourceCurrentMemoMergeResourceControl.initialBound source.nodes.next source.edges.next
  (InternedValueMassHeap.initialBound source)

private theorem constructed : built = .done original source := by cbv
private theorem source_semantic : SemanticReady source :=
  SourceEqualityRequiredSemanticCache.constructed expression original source constructed
private theorem source_available : Available source original :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result original source constructed
private theorem inner_member : inner ∈ children original := by cbv; exact .head _
private theorem inner_available : Available source inner := source_available.children inner inner_member
private theorem actual : unfolded = .done exposed heap := by cbv
private theorem inner_shape : ∃ entry body depth ordinary, inner = Value.mu entry body depth ordinary := by
  have shape : (match inner with | .mu .. => True | _ => False) := by cbv
  cases found : inner with
  | mu entry body depth ordinary => exact ⟨entry, body, depth, ordinary, rfl⟩
  | empty | reference | node | union => simp only [found] at shape
private theorem exposed_shape : ∃ entry rows depth free, exposed = Value.node entry rows depth free := by
  have shape : (match exposed with | .node .. => True | _ => False) := by cbv
  cases found : exposed with
  | node entry rows depth free => exact ⟨entry, rows, depth, free, rfl⟩
  | empty | reference | mu | union => simp only [found] at shape
private theorem inner_open : inner.free ≠ [] := by cbv; intro impossible; cases impossible
private theorem exposed_open : exposed.free ≠ [] := by cbv; intro impossible; cases impossible
private theorem after_properties :
    SourceEqualityRequiredCache.Keeps source heap ∧ SemanticReady heap ∧ Available heap exposed := by
  obtain ⟨value, after, done, keeps, semantic, available, _⟩ :=
    SourceEqualityOpenOrdinaryHead.unfold_complete inner source source_semantic inner_available
  obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
  subst value
  subst after
  exact ⟨keeps, semantic, available⟩
private theorem warm_actual : InternedFreshOrdinaryStoredSubstitution.unfold inner heap = .done exposed heap :=
  InternedFreshOrdinaryStoredSubstitution.unfold_replay inner source heap exposed heap
    source_semantic.ready.semantic.1.normal.facts.coherent.valid actual (grows_refl _)

private theorem initial_fits : Fits scalar source :=
  SourceCurrentMemoMergeResourceControl.initial source _
    (InternedValueMassHeap.initial source source_semantic.ready.semantic.1.normal.facts)
private theorem source_costs : InternedFreshOrdinaryCostHeap.Heap source :=
  InternedFreshOrdinaryCosts.closed_heap expression
private theorem source_values : InternedNestedProvenance.Values source [inner] := by
  intro value member
  simpa only [List.mem_singleton.mp member] using inner_available

private theorem missing_edges (rows : List (EdgeValue Nat Bool))
    (state : State Nat Bool) (missing : ∀ edge ∈ rows, edge.children[99]? = none) :
    EdgesTrace (fun _ => true) 99 [] rows state false state := by
  induction rows with
  | nil => exact .nil
  | cons first rest ih =>
      exact .next (.missing (missing first (List.mem_cons_self)))
        (ih (fun edge member => missing edge (List.mem_cons_of_mem _ member)))

private theorem cold_missing : NodeTrace (fun _ => true) [99] inner source false heap := by
  obtain ⟨entry, body, depth, ordinary, shape⟩ := inner_shape
  obtain ⟨own, rows, level, free, nextShape⟩ := exposed_shape
  have openInner : (Value.mu entry body depth ordinary).free.isEmpty = false := by
    rw [← shape]
    cases freeEq : inner.free with
    | nil => exact False.elim (inner_open freeEq)
    | cons first rest => rfl
  have openNext : free.isEmpty = false := by
    have opened := exposed_open
    rw [nextShape] at opened
    cases free <;> simp_all [Value.free]
  have missing : ∀ edge ∈ rows, edge.children[99]? = none := by
    have exactRows : rows = (match exposed with | .node _ rows _ _ => rows | _ => []) := by rw [nextShape]
    have checked : (match exposed with | .node _ rows _ _ => rows | _ => []).all
        (fun edge => edge.children[99]?.isNone) = true := by cbv
    rw [← exactRows] at checked
    intro edge member
    have absent := List.all_eq_true.mp checked edge member
    cases found : edge.children[99]? <;> simp_all
  rw [shape]
  refine .unfold (next := exposed) (after := heap) rfl openInner ?_ ?_
  · simpa only [unfolded, shape] using actual
  · rw [nextShape]
    exact .branches (by simp only [openNext, Bool.and_false]) (missing_edges rows heap missing)

private theorem warm_endpoint : NodeTrace (fun _ => true) [] inner heap true heap := by
  obtain ⟨entry, body, depth, ordinary, shape⟩ := inner_shape
  obtain ⟨own, rows, level, free, nextShape⟩ := exposed_shape
  have openInner : (Value.mu entry body depth ordinary).free.isEmpty = false := by
    rw [← shape]
    cases freeEq : inner.free with
    | nil => exact False.elim (inner_open freeEq)
    | cons first rest => rfl
  have openNext : free.isEmpty = false := by
    have opened := exposed_open
    rw [nextShape] at opened
    cases free <;> simp_all [Value.free]
  rw [shape]
  refine .unfold (next := exposed) (after := heap) rfl openInner ?_ ?_
  · simpa only [shape] using warm_actual
  · rw [nextShape]
    simpa only [openNext, Bool.not_false] using
      (NodeTrace.endpoint (unconstrained := fun _ => true)
        (entry := own) (edges := rows) (depth := level) (free := free) (state := heap)
        (by simp only [openNext, Bool.and_false]))

/-- Initial source writes give a cold open-Mu scan and an exact subsequent warm unfold. -/
theorem constructed_cold_then_warm :
    ∃ (value : Value Nat Bool) (before after : State Nat Bool) (q : Nat),
      value.free ≠ [] ∧ before ≠ after ∧
      InternedFreshOrdinaryStoredSubstitution.unfold value after = .done exposed after ∧
      ClassTrace (fun _ => true) [value] [[0,99],[0]] before true after ∧
      Fits (classBound [[0,99],[0]] q) after ∧
      SourceEqualityRequiredCache.Keeps before after ∧
      ∀ fuel, classFuel [[0,99],[0]] q ≤ fuel →
        classMeets (fun _ => true) fuel [value] [[0,99],[0]] before = .done (some true) after := by
  obtain ⟨answer, after, graph, _semantic, _costs, kept, _values, fits, worker⟩ :=
    class_complete (fun _ => true) [inner] [[0,99],[0]] source source_semantic source_costs source_values scalar initial_fits
  have expected : ClassTrace (fun _ => true) [inner] [[0,99],[0]] source true heap :=
    .next (.child (.present rfl cold_missing)) (.stop (.child (.present rfl warm_endpoint)))
  obtain ⟨rfl, rfl⟩ := class_trace_unique _ _ _ _ _ _ _ _ graph expected
  refine ⟨inner, source, heap, scalar, inner_open, ?_, warm_actual, graph, fits, kept, worker⟩
  intro equal
  have counts := congrArg (fun state : State Nat Bool => state.nodes.next) equal
  cbv at counts

/-- The actual secondary source policy distinguishes a closed constrained endpoint from its interior. -/
theorem constructed_constrained_endpoint :
    ∃ (value : Value Nat Bool) (before : State Nat Bool) (q : Nat),
      value.free = [] ∧
      ClassTrace (fun _ => false) [value] [[0]] before false before ∧
      ClassTrace (fun _ => false) [value] [[0,0]] before true before ∧
      Fits (classBound [[0]] q) before ∧ Fits (classBound [[0,0]] q) before ∧
      (∀ fuel, classFuel [[0]] q ≤ fuel →
        classMeets (fun _ => false) fuel [value] [[0]] before = .done (some false) before) ∧
      (∀ fuel, classFuel [[0,0]] q ≤ fuel →
        classMeets (fun _ => false) fuel [value] [[0,0]] before = .done (some true) before) := by
  have sourceValues : InternedNestedProvenance.Values source [original] := by
    intro value member
    simpa only [List.mem_singleton.mp member] using source_available
  have closed : original.free = [] := by cbv
  have shape : ∃ entry body depth ordinary, original = Value.mu entry body depth ordinary := by
    have mu : (match original with | .mu .. => True | _ => False) := by cbv
    cases found : original with
    | mu entry body depth ordinary => exact ⟨entry,body,depth,ordinary,rfl⟩
    | empty | reference | node | union => simp only [found] at mu
  obtain ⟨a, s, endpoint, _, _, _, _, endpointFits, endpointWorker⟩ :=
    class_complete (fun _ => false) [original] [[0]] source source_semantic source_costs sourceValues scalar initial_fits
  obtain ⟨b, t, interior, _, _, _, _, interiorFits, interiorWorker⟩ :=
    class_complete (fun _ => false) [original] [[0,0]] source source_semantic source_costs sourceValues scalar initial_fits
  obtain ⟨entry,body,depth,ordinary,mu⟩ := shape
  have endpointNode : NodeTrace (fun _ => false) [] original source false source := by
    rw [mu]
    have free : (Value.mu entry body depth ordinary).free.isEmpty = true := by rw [← mu, closed]; rfl
    simpa only [free, Bool.not_true] using
      (NodeTrace.constrained (unconstrained := fun _ => false) (path := []) (state := source)
        (entry := entry) (body := body) (depth := depth) (ordinary := ordinary) rfl)
  have interiorNode : NodeTrace (fun _ => false) [0] original source true source := by
    rw [mu]
    exact .constrained rfl
  have expectedEndpoint : ClassTrace (fun _ => false) [original] [[0]] source false source :=
    .next (.child (.present rfl endpointNode)) .nil
  have expectedInterior : ClassTrace (fun _ => false) [original] [[0,0]] source true source :=
    .stop (.child (.present rfl interiorNode))
  obtain ⟨rfl, rfl⟩ := class_trace_unique _ _ _ _ _ _ _ _ endpoint expectedEndpoint
  obtain ⟨rfl, rfl⟩ := class_trace_unique _ _ _ _ _ _ _ _ interior expectedInterior
  exact ⟨original, source, scalar, closed, endpoint, interior, endpointFits, interiorFits, endpointWorker, interiorWorker⟩
end MicroCFTA.SecondaryNumericKernels

#print axioms MicroCFTA.SecondaryNumericKernels.constructed_cold_then_warm
#check @MicroCFTA.SecondaryNumericKernels.constructed_cold_then_warm
#print axioms MicroCFTA.SecondaryNumericKernels.constructed_constrained_endpoint
#check @MicroCFTA.SecondaryNumericKernels.constructed_constrained_endpoint
