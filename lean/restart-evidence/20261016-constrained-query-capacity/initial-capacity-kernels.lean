import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryInitialCapacity
import MicroCFTA.SourceCurrentAllocatedTargetQuery

namespace FiniteOrdinaryInitialCapacityKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedFiniteOrdinaryConstructionReservations (nodeCount edgeCount)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Static source counts construct admission and the first exact native query without future capacity input. -/
theorem first_query (bits : Nat) {initial final : Cache.State Key} {originals : List Guard}
    (history : SourceEqualityOriginalAllocationHistory.History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (nodes : nodeCount expression ≤ 2 ^ bits) (edges : edgeCount expression ≤ 2 ^ (bits + 2))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      DNode value ∧ ∃ next result after,
        SourceCurrentAllocatedTargetQuery.Receipt formulas solver next value value
          (caller (bits + 2) final heap).checked result after globals := by
  obtain ⟨value, heap, built, context, _stored, resultDomain, capacity, _identity, _same, _inherited, available, closed, _original⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryInitialCapacity.constructed bits history valid expression domain covered
      nodes edges formulas solver
  have words := SourceCurrentAllocatedFiniteOrdinaryCapacity.node_words bits (caller (bits + 2) final heap).checked
    context.ready.good value value available available resultDomain resultDomain capacity
  obtain ⟨next, result, after, _source, _roots, receipt⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver (inventory expression value heap built) value value (caller (bits + 2) final heap).checked
    context.ready context.admitted available available closed closed words globals context.globals
  exact ⟨value, heap, built, resultDomain, next, result, after, receipt⟩

/-- Actual field preparation retains the syntax-derived capacity in the same complete initial caller. -/
theorem prepared_admission (bits : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (nodes : nodeCount expression ≤ 2 ^ bits) (edges : edgeCount expression ≤ 2 ^ (bits + 2))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        SourceCurrentAllocatedPartialInvariant.Context formulas solver (inventory expression value heap built)
          (caller (bits + 2) cache heap) globals ∧
        SourceCurrentAllocatedFiniteOrdinaryOuterState.Stored (caller (bits + 2) cache heap) ∧
        DNode value ∧ SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits (caller (bits + 2) cache heap).checked := by
  obtain ⟨fields, receipt, value, heap, built, context, stored, resultDomain, capacity, _⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryInitialCapacity.prepared bits initial valid expression domain cached
      nodes edges formulas solver
  exact ⟨fields, receipt, value, heap, built, context, stored, resultDomain, capacity⟩

end FiniteOrdinaryInitialCapacityKernels
#print axioms FiniteOrdinaryInitialCapacityKernels.first_query
#check @FiniteOrdinaryInitialCapacityKernels.first_query
#print axioms FiniteOrdinaryInitialCapacityKernels.prepared_admission
#check @FiniteOrdinaryInitialCapacityKernels.prepared_admission
