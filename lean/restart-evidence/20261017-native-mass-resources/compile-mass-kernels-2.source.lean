import MicroCFTA.SourceRecursiveIntersectionCompileMass
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace MicroCFTA.CompileMassIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Stored" => InternedValueMassHeap.Stored
local notation "inflate" => InternedFreshOrdinaryResultMass.inflate
local notation "interpret" => SourceRecursiveIntersectionCode.interpret

private theorem repeat_trace (call : A → Machine Symbol Guard → Result Symbol Guard B)
    (request : A) (value : B) (state : Machine Symbol Guard)
    (once : call request state = .done value state) (count : Nat) :
    WalkTrace call (List.replicate count request) state (List.replicate count value) state := by
  induction count with
  | zero => exact .nil state
  | succ count ih => exact .cons _ _ _ _ _ _ _ once ih

private def row : EdgeValue Nat Bool := (InternedConstructorTemplates.run (makeEdge 0 true []) empty).1
private def heap : State Nat Bool := (InternedConstructorTemplates.run (makeEdge 0 true []) empty).2
private def machine : Machine Nat Bool := ⟨heap, Cache.emptyState⟩
private def nodes : SourceRecursiveIntersectionCode.NodeCall Nat Bool :=
  fun request => execute true (fun first second => first && second) 0 request.domain request.left request.right
private def edges : SourceRecursiveIntersectionCode.EdgeCall Nat Bool :=
  fun request => edge true (fun first second => first && second)
    (fun left right => nodes ⟨request.domain, left, right⟩) request.left request.right

/-- Six literal zero-arity edge calls precede their own compiled node construction. -/
theorem repeated_rows :
    ∃ value after,
      (pairs [row, row] [row, row, row]).length = 6 ∧
      interpret nodes edges (SourceRecursiveIntersectionCode.compileRows IntersectionEmptyDomain.emptyDomain
        [row, row] [row, row, row]) machine = .done value after ∧
      after.domains = machine.domains ∧
      Stored (inflate 6 (InternedValueMassHeap.initialBound heap)) after.heap ∧
      InternedValueMass.value value ≤ inflate 6 (InternedValueMassHeap.initialBound heap) ∧
      after.heap.nodes.next ≤ heap.nodes.next + 1 ∧ after.heap.edges.next = heap.edges.next := by
  have checked := InternedNestedFacts.edge_verified 0 true ([] : List (Value Nat Bool)) empty empty_facts
    (by intro value member; cases member)
  have stored := InternedValueMassHeap.initial heap checked.facts
  have resident : EdgeResident heap row := checked.result row heap rfl
  have requests : pairs [row, row] [row, row, row] = List.replicate 6 (row, row) := by rfl
  have once : edges ⟨IntersectionEmptyDomain.emptyDomain, row, row⟩ machine = .done row machine := by rfl
  have trace : WalkTrace (fun rows => edges ⟨IntersectionEmptyDomain.emptyDomain, rows.1, rows.2⟩)
      (pairs [row, row] [row, row, row]) machine (List.replicate 6 row) machine := by
    rw [requests]
    exact repeat_trace (fun rows : EdgeValue Nat Bool × EdgeValue Nat Bool =>
      edges ⟨IntersectionEmptyDomain.emptyDomain, rows.1, rows.2⟩) (row, row) row machine once 6
  obtain ⟨value, after, done, domain, resultStored, mass, count, edgeCount⟩ :=
    SourceRecursiveIntersectionCompileMass.compileRows nodes edges IntersectionEmptyDomain.emptyDomain
      [row, row] [row, row, row] machine machine (List.replicate 6 row) _ trace stored
      (by intro edge member; have same := List.eq_of_mem_replicate member; exact same ▸ resident)
  exact ⟨value, after, rfl, done, domain, resultStored, mass, count, edgeCount⟩

private def fixture : Syntax Nat Bool :=
  .union [.binder false (.node [.mk 2 true [.var 0]]), .node [.mk 3 false []]]

/-- An actual constructed mixed union supplies its original members to actual empty queries and the union suffix. -/
theorem constructed_union :
    ∃ original members source value after,
      InternedFreshOrdinaryConstruction.build fixture [] empty = .done original source ∧
      (match original with | .union _ captured _ _ => captured = members | _ => False) ∧
      members.length = 2 ∧
      interpret (fun request => execute true (fun first second => first && second) 1 request.domain request.left request.right)
          edges
          ((SourceRecursiveIntersectionCode.walk (fun member => SourceRecursiveIntersectionCode.requestNode
            IntersectionEmptyDomain.emptyDomain member .empty) members).bind fun values => .work (makeUnion values) .pure)
          ⟨source, Cache.emptyState⟩ = .done value after ∧
      Stored (inflate 2 (InternedValueMassHeap.initialBound source)) after.heap ∧
      InternedValueMass.value value ≤ inflate 2 (InternedValueMassHeap.initialBound source) ∧
      after.heap.nodes.next ≤ source.nodes.next + 1 ∧ after.heap.edges.next = source.edges.next := by
  obtain ⟨original, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete fixture
  have facts := InternedFreshOrdinaryFacts.build_verified fixture [] empty empty_facts
    (by intro value member; cases member)
  have sourceFacts : Facts source := by simpa only [built, Outcome.state] using facts.facts
  have available := facts.result original source built
  have shape : (match InternedFreshOrdinaryConstruction.build fixture [] empty with
      | .done (.union _ members _ _) _ => decide (members.length = 2)
      | _ => false) = true := by
    set_option cbv.maxSteps 200000000 in cbv
  rw [built] at shape
  cases original with
  | union entry members level free =>
      have length : members.length = 2 := by simpa only [decide_eq_true_eq] using shape
      let before : Machine Nat Bool := ⟨source, Cache.emptyState⟩
      let calls : SourceRecursiveIntersectionCode.NodeCall Nat Bool :=
        fun request => execute true (fun first second => first && second) 1 request.domain request.left request.right
      have once (member : Value Nat Bool) : calls ⟨IntersectionEmptyDomain.emptyDomain, member, .empty⟩ before = .done .empty before := by
        cases member <;> rfl
      have trace : WalkTrace (fun member => calls ⟨IntersectionEmptyDomain.emptyDomain, member, .empty⟩)
          members before (List.replicate members.length .empty) before := by
        clear built available shape length
        induction members with
        | nil => exact .nil before
        | cons first rest ih => exact .cons _ _ _ _ _ _ _ (once first) ih
      have stored := InternedValueMassHeap.initial source sourceFacts
      obtain ⟨value, after, done, _domain, finalStored, mass, count, edgeCount⟩ :=
        SourceRecursiveIntersectionCompileMass.union calls edges IntersectionEmptyDomain.emptyDomain members .empty true
          before before (List.replicate members.length .empty) _ trace stored
          (by intro value member; have same := List.eq_of_mem_replicate member; exact same ▸ empty_available source)
      refine ⟨.union entry members level free, members, source, value, after, built, rfl, length, ?_, ?_, ?_, count, edgeCount⟩
      · simpa only [ite_true] using done
      · simpa only [length] using finalStored
      · simpa only [length] using mass
  | empty | reference | node | mu => cases shape

end MicroCFTA.CompileMassIntegration

#print axioms MicroCFTA.CompileMassIntegration.repeated_rows
#check @MicroCFTA.CompileMassIntegration.repeated_rows
#print axioms MicroCFTA.CompileMassIntegration.constructed_union
#check @MicroCFTA.CompileMassIntegration.constructed_union
