import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNumericRoot

namespace MicroCFTA.NumericRootIndependentIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialGraph (NodeCall)
open SourceCurrentAllocatedPartialSourceReads (NodeCallReads)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Plan" => SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Actual preparation retains initial capacity and key safety beside the same root return and exact language. -/
theorem prepared_initial_words (bits : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (nodes : SourceCurrentAllocatedFiniteOrdinaryConstructionReservations.nodeCount expression ≤ 2 ^ bits)
    (edges : SourceCurrentAllocatedFiniteOrdinaryConstructionReservations.edgeCount expression ≤ 2 ^ (bits + 2))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (ranges : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Plan bits budget (.nodeCall ⟨emptyValue (SourceEqualityOriginalAllocationPreparation.prepare
        (SourceEqualityConstraintOrigins.guards expression) initial).2, value⟩
        (caller (bits + 2) (SourceEqualityOriginalAllocationPreparation.prepare
          (SourceEqualityConstraintOrigins.guards expression) initial).2 heap))) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits (caller (bits + 2) cache heap).checked ∧
        SourceCurrentAllocatedNativeRequestBounds.WordRanges
          (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain value value))
          (caller (bits + 2) cache heap).checked ∧
        ∃ result after next final,
          ∃ actual : NodeCall budget ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap) result after,
            NodeCallReads formulas solver actual globals final ∧
            Post formulas solver next (caller (bits + 2) cache heap) after final ∧ Stored after ∧
            ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  dsimp only
  obtain ⟨fields, prepared, value, heap, built, capacity,
      result, after, next, final, stable, actual, reads, checks, post, output, stored, narrowed, exactLanguage⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterNumericRoot.bounded_prepared_root bits initial valid expression domain
      cached nodes edges formulas solver budget ranges
  have initialized := SourceCurrentAllocatedPartialInitialization.constructed (bits + 2) prepared.history valid
    expression (fun _ member => member) value heap built formulas solver
  have resident := (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built
  have resultDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node value := by
    obtain ⟨original, originalHeap, sameBuild, originalDomain, facts, available⟩ :=
      SourceCurrentAllocatedFiniteOrdinaryConstruction.closed expression domain
    have same := InternedNestedConstruction.Outcome.done.inj (sameBuild.symm.trans built)
    simpa only [same.1] using originalDomain
  have words := SourceCurrentAllocatedFiniteOrdinaryCapacity.node_words bits _ initialized.1.ready.good
    value value resident resident resultDomain resultDomain capacity
  exact ⟨fields, prepared, value, heap, built, capacity, words,
    result, after, next, final, actual, reads, post, stored, exactLanguage⟩

end MicroCFTA.NumericRootIndependentIntegration

#print axioms MicroCFTA.NumericRootIndependentIntegration.prepared_initial_words
#check @MicroCFTA.NumericRootIndependentIntegration.prepared_initial_words
