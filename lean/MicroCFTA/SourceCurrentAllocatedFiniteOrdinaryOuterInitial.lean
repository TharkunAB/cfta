import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstruction
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterState
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceEqualityOriginalAllocationPreparation

/-!
# Constructed finite ordinary caller admission

Ordinary source syntax constructs its own complete root and domain.
Actual field history supplies the semantic initial context.
Cold native, merge, and outer tables derive their structural certificates.
This logical initialization does not reset a Haskell global cache.
Outer execution and its machine ranges remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterInitial
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Literal cold initialization derives all three structural certificates over the actual retained heap. -/
theorem stored (width : Nat) (cache : Cache.State Key) (heap : State Symbol Guard) :
    Stored (caller width cache heap) :=
  SourceCurrentAllocatedFiniteOrdinaryOuterState.initial _ _ _
    (SourceCurrentAllocatedFiniteOrdinaryStored.initial_stored width ⟨heap, Cache.emptyState⟩)
    SourceCurrentAllocatedFiniteOrdinaryMergeCache.empty_stored

/-- Covered fields and ordinary source syntax construct the root and its complete initial admission. -/
theorem constructed
    (width : Nat) {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Context formulas solver (inventory expression value heap built) (caller width final heap) globals ∧
      Stored (caller width final heap) ∧ DNode value ∧
      ∃ identity, emptyValue final = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready (caller width final heap).checked.operations.constraints (.live identity []) ∧
        Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  obtain ⟨value, heap, built, resultDomain, _facts, _available⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryConstruction.closed expression domain
  obtain ⟨context, inherited⟩ := SourceCurrentAllocatedPartialInitialization.constructed width history valid
    expression covered value heap built formulas solver
  exact ⟨value, heap, built, context, stored width final heap, resultDomain, inherited⟩

/-- Literal field preparation derives history before source construction and cold structural admission. -/
theorem prepared
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        Context formulas solver (inventory expression value heap built) (caller width cache heap) globals ∧
        Stored (caller width cache heap) ∧ DNode value ∧
        ∃ identity, emptyValue cache = .live identity [] ∧
          SourceEqualityConstraintAllocation.Ready (caller width cache heap).checked.operations.constraints (.live identity []) ∧
          Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  let cache := (SourceEqualityOriginalAllocationPreparation.prepare
    (SourceEqualityConstraintOrigins.guards expression) initial).2
  obtain ⟨fields, final, receipt⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete
    (SourceEqualityConstraintOrigins.guards expression) initial valid cached
  have same : cache = final := congrArg Prod.snd receipt.done
  have actual : SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache := by simpa only [same] using receipt
  exact ⟨fields, actual, constructed width actual.history valid expression domain (fun _ member => member) formulas solver⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterInitial
