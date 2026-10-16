import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterInitial

namespace FiniteOrdinaryInitialReviewChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance

/-- Full guards at two ordinary constructor depths need no empty-equality restriction. -/
theorem generic_nested {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (outer inner : Symbol) (outerGuard innerGuard : Guard) :
    let expression : InternedNestedConstruction.Syntax Symbol Guard :=
      .node [.mk outer outerGuard [.node [.mk inner innerGuard []]]]
    ∃ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧ InternedNestedFacts.Facts heap ∧ Available heap value := by
  exact SourceCurrentAllocatedFiniteOrdinaryConstruction.closed _ (.ordinary (.cons (.cons (.ordinary (.cons .nil .nil)) .nil) .nil))

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
open SourceCurrentAllocatedPartialInitialization

/-- Actual preparation retains its interner, then actual Empty allocation grows it before cold table admission. -/
theorem prepared_context [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        SourceCurrentAllocatedPartialInvariant.Context formulas solver (inventory expression value heap built) (caller width cache heap) globals ∧
        SourceCurrentAllocatedFiniteOrdinaryOuterState.Stored (caller width cache heap) ∧
        SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧
        (caller width cache heap).checked.native.machine.heap = heap ∧
        SourceEqualityConstraintMemoAllocation.Grows (SourceEqualityConstraintMemoAllocation.initial cache)
          (caller width cache heap).checked.operations ∧
        ∃ identity, emptyValue cache = .live identity [] ∧
          SourceEqualityConstraintAllocation.Ready (caller width cache heap).checked.operations.constraints (.live identity []) ∧
          Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  obtain ⟨fields, prepared, value, heap, built, context, stored, resultDomain, inherited⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.prepared width initial valid expression domain cached formulas solver
  exact ⟨fields, prepared, value, heap, built, context, stored, resultDomain, rfl,
    (operations_correct _ prepared.valid).2.1, inherited⟩

#print axioms generic_nested
#check @generic_nested
#print axioms prepared_context
#check @prepared_context
end FiniteOrdinaryInitialReviewChecks
