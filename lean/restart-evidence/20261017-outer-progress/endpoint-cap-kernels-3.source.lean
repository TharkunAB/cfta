import MicroCFTA.SourceCurrentPrimaryEndpointCap
import MicroCFTA.SourceEqualityRequiredSemanticCache
import MicroCFTA.SourceCurrentMuEndpoint

namespace MicroCFTA.EndpointCapConstructed
open InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Plain" => fun guard : Guard => SourceMemoGate.plain guard = true
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := ⟨some [], .top⟩
private def equal : Guard := ⟨some [[[0], [1]]], .top⟩
private def recursive : Syntax Symbol Guard := .binder false (.node [.mk ("step", .top) top [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("pair", .top) equal [recursive, recursive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def input : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem built_done : built = .done input heap := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression input heap built_done
private theorem available : Available heap input :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result input heap built_done
private theorem endpoint_done : EndpointStatefulGate.nodeMeets source reaches 1 [] input heap = .done (some false) heap := by cbv
private theorem endpoint_trace : EndpointStatefulGateTrace.NodeTrace source reaches [] input heap false heap :=
  EndpointStatefulGateTrace.node_trace_of_done source reaches 1 [] input heap false heap endpoint_done
private theorem not_cap_zero : ¬SourceCurrentConstrainedCap.Cap Plain 0 input := by
  intro bounded
  have plain := SourceCurrentHereditaryUnconstrained.unconstrained input (bounded.annotated rfl)
  have constrained : source input = false := by cbv
  rw [constrained] at plain
  cases plain
private theorem open_available : Available heap (.reference .depth) :=
  reference_available heap .depth (by intro identity member; simp only [Value.free, List.mem_singleton] at member; cases member)

/-- An own constructed constrained endpoint contains plain recursion and needs positive cap depth. -/
theorem constructed_positive_endpoint :
    ∃ (program : Syntax Symbol Guard) (value : Value Symbol Guard) (initial : Heap),
      InternedFreshOrdinaryConstruction.build program [] empty = .done value initial ∧
      SourceEqualityRequiredSemanticCache.SemanticReady initial ∧ Available initial value ∧ value.free = [] ∧
      value.depth = 1 ∧ source value = false ∧ reaches value = false ∧
      SourceCurrentMuEndpoint.classMeets true source reaches 1 [value, .reference .depth] [[0]] initial =
        .done (some false) initial ∧
      SourceCurrentConstrainedCap.Cap Plain (InternedValueMass.value value) value ∧
      ¬SourceCurrentConstrainedCap.Cap Plain 0 value ∧
      Available initial (.reference .depth) ∧ (Value.reference .depth : Value Symbol Guard).free ≠ [] := by
  refine ⟨expression, input, heap, built_done, semantic, available, by cbv, by cbv, by cbv,
    SourceCurrentPrimaryEndpointCap.endpoint_clear endpoint_trace, by cbv,
    SourceCurrentPrimaryEndpointCap.endpoint_cap heap semantic.ready.semantic.1.normal.facts.coherent input available endpoint_trace,
    not_cap_zero, open_available, by simp only [Value.free, List.cons_ne_nil]⟩

end MicroCFTA.EndpointCapConstructed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000

#check @MicroCFTA.EndpointCapConstructed.constructed_positive_endpoint
#print MicroCFTA.EndpointCapConstructed.constructed_positive_endpoint
#print axioms MicroCFTA.EndpointCapConstructed.constructed_positive_endpoint
