import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructionReservations
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterInitial
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCapacity

/-!
# Static initial capacity for constructed finite ordinary roots

Syntax counts bound the actual source construction supplies.
The same completed heap supplies the initial caller and its full context.
Field preparation retains that heap and its two constructor counters.
This result does not bound later Target or Leaf query entries.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryInitialCapacity
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryCapacity (Capacity)
open SourceCurrentAllocatedFiniteOrdinaryConstructionReservations (nodeCount edgeCount)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] in
/-- Static source syntax bounds derive numeric capacity at the exact constructed initial heap. -/
theorem built_capacity (bits : Nat) (cache : Cache.State Key)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (nodes : nodeCount expression ≤ 2 ^ bits) (edges : edgeCount expression ≤ 2 ^ (bits + 2)) :
    Capacity bits (caller (bits + 2) cache heap).checked := by
  have bounds := SourceCurrentAllocatedFiniteOrdinaryConstructionReservations.build_bounds expression domain [] empty value heap built
  have nodeBound : heap.nodes.next ≤ nodeCount expression := by
    simpa only [empty, Cache.emptyState, Nat.zero_add] using bounds.1
  have edgeBound : heap.edges.next ≤ edgeCount expression := by
    simpa only [empty, Cache.emptyState, Nat.zero_add] using bounds.2
  exact ⟨Nat.le_trans nodeBound nodes, Nat.le_trans edgeBound edges⟩

/-- Covered source syntax constructs the root, its initial context, and capacity from static counts. -/
theorem constructed (bits : Nat) {initial final : Cache.State Key} {originals : List Guard}
    (history : SourceEqualityOriginalAllocationHistory.History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (nodes : nodeCount expression ≤ 2 ^ bits) (edges : edgeCount expression ≤ 2 ^ (bits + 2))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Context formulas solver (inventory expression value heap built) (caller (bits + 2) final heap) globals ∧
      Stored (caller (bits + 2) final heap) ∧ DNode value ∧ Capacity bits (caller (bits + 2) final heap).checked ∧
      ∃ identity, emptyValue final = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready (caller (bits + 2) final heap).checked.operations.constraints (.live identity []) ∧
        Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  obtain ⟨value, heap, built, context, stored, resultDomain, inherited⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.constructed (bits + 2) history valid expression domain covered formulas solver
  exact ⟨value, heap, built, context, stored, resultDomain,
    built_capacity bits final expression domain value heap built nodes edges, inherited⟩

/-- Actual field preparation constructs the same admitted root and initial static capacity. -/
theorem prepared (bits : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
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
        Context formulas solver (inventory expression value heap built) (caller (bits + 2) cache heap) globals ∧
        Stored (caller (bits + 2) cache heap) ∧ DNode value ∧ Capacity bits (caller (bits + 2) cache heap).checked ∧
        ∃ identity, emptyValue cache = .live identity [] ∧
          SourceEqualityConstraintAllocation.Ready (caller (bits + 2) cache heap).checked.operations.constraints (.live identity []) ∧
          Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  obtain ⟨fields, fieldsReceipt, value, heap, built, context, stored, resultDomain, inherited⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.prepared (bits + 2) initial valid expression domain cached formulas solver
  exact ⟨fields, fieldsReceipt, value, heap, built, context, stored, resultDomain,
    built_capacity bits _ expression domain value heap built nodes edges, inherited⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryInitialCapacity
