import MicroCFTA.SourceRecursiveIntersectionCompileWidth
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

namespace MicroCFTA.CompileWidthIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open InternedNestedConstruction (Syntax Outcome)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "At" => SourceRecursiveIntersectionCodeMass.At
local notation "initialBound" => InternedValueMassHeap.initialBound
local notation "inflate" => InternedFreshOrdinaryResultMass.inflate

private def fixture : Syntax Nat Bool :=
  .node [.mk 99 true [
    .binder false (.node [.mk 0 true [.var 0]]),
    .union [.binder false .empty, .node [.mk 1 false []]],
    .node [.mk 2 true []], .node [.mk 2 false []]]]

private def kind : Value Nat Bool → Nat
  | .empty => 0
  | .reference _ => 1
  | .node _ _ _ _ => 2
  | .union _ _ _ _ => 3
  | .mu _ _ _ _ => 4

private theorem source :
    ∃ value heap,
      InternedFreshOrdinaryConstruction.build fixture [] empty = .done value heap ∧
      Facts heap ∧ Available heap value ∧
      ((children value).map kind) = [4, 3, 2, 2] := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete fixture
  have checked := InternedFreshOrdinaryFacts.build_verified fixture [] empty empty_facts
    (by intro value member; cases member)
  have facts : Facts heap := by simpa only [built, Outcome.state] using checked.facts
  have shape : (match InternedFreshOrdinaryConstruction.build fixture [] empty with
      | .done value _ => decide (((children value).map kind) = [4, 3, 2, 2])
      | .pending _ _ => false) = true := by
    set_option cbv.maxSteps 200000000 in cbv
  have kinds : ((children value).map kind) = [4, 3, 2, 2] := by
    simpa only [built, decide_eq_true_eq] using shape
  exact ⟨value, heap, built, facts, checked.result value heap built, kinds⟩

/-- One actual mixed source produces quantitative code certificates for every ordered operand pair. -/
theorem constructed_dispatch :
    ∃ root heap,
      InternedFreshOrdinaryConstruction.build fixture [] empty = .done root heap ∧
      ((children root).map kind) = [4, 3, 2, 2] ∧
      ∀ left ∈ children root, ∀ right ∈ children root,
        At (SourceRecursiveIntersectionCode.compileNode ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩)
          ⟨heap, Cache.emptyState⟩ (initialBound heap) (fun after value => Available after.heap value) := by
  obtain ⟨root, heap, built, facts, available, kinds⟩ := source
  have stored := InternedValueMassHeap.initial heap facts
  refine ⟨root, heap, built, kinds, ?_⟩
  intro left leftMember right rightMember
  exact SourceRecursiveIntersectionCompileWidth.compileNode _ _ _ ⟨facts, Cache.empty_valid⟩ stored
    ⟨empty_domain _, available.children left leftMember, available.children right rightMember⟩

/-- A real constructor prefix supplies its own larger store before the same original compiled requests. -/
theorem constructed_growth :
    ∃ root heap row after,
      InternedFreshOrdinaryConstruction.build fixture [] empty = .done root heap ∧
      ((children root).map kind) = [4, 3, 2, 2] ∧
      InternedConstructorTemplates.run (makeEdge 100 true [root]) heap = (row, after) ∧
      Stored (inflate 1 (initialBound heap)) after ∧
      initialBound heap ≤ inflate 1 (initialBound heap) ∧
      ∀ left ∈ children root, ∀ right ∈ children root,
        At (SourceRecursiveIntersectionCode.compileNode ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩)
          ⟨after, Cache.emptyState⟩ (inflate 1 (initialBound heap)) (fun final value => Available final.heap value) := by
  obtain ⟨root, heap, built, facts, available, kinds⟩ := source
  have stored := InternedValueMassHeap.initial heap facts
  let actual := InternedConstructorTemplates.run (makeEdge 100 true [root]) heap
  have checked := InternedNestedFacts.edge_verified 100 true [root] heap facts (by
    intro value member
    cases List.mem_singleton.mp member
    exact available)
  have sizes := SourceRecursiveIntersectionWorkMass.edge 100 true [root] heap stored (by
    intro value member
    cases List.mem_singleton.mp member
    exact InternedValueMassHeap.available heap stored root available)
  have current : Stored (inflate 1 (initialBound heap)) actual.2 := sizes.1
  refine ⟨root, heap, actual.1, actual.2, built, kinds, rfl, current,
    InternedFreshOrdinaryResultMass.inflate_ge _ _, ?_⟩
  intro left leftMember right rightMember
  have leftAvailable := (available.children left leftMember).grows heap actual.2 checked.growth checked.history
  have rightAvailable := (available.children right rightMember).grows heap actual.2 checked.growth checked.history
  exact SourceRecursiveIntersectionCompileWidth.compileNode _ _ _ ⟨checked.facts, Cache.empty_valid⟩ current
    ⟨empty_domain _, leftAvailable, rightAvailable⟩

end MicroCFTA.CompileWidthIntegration

#print axioms MicroCFTA.CompileWidthIntegration.constructed_dispatch
#check @MicroCFTA.CompileWidthIntegration.constructed_dispatch
#print axioms MicroCFTA.CompileWidthIntegration.constructed_growth
#check @MicroCFTA.CompileWidthIntegration.constructed_growth
