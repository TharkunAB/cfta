import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRoot

namespace FiniteOrdinaryRootIndependentChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialGraph (NodeCall)
open SourceCurrentAllocatedPartialSourceReads (NodeCallReads)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "Plan" => SourceCurrentAllocatedFiniteOrdinaryOuterEntries.Plan
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Actual field preparation and initial entry checks construct a closed exact-language root return at fixed conjunction budget zero. -/
theorem prepared_zero_budget
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ranges : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Plan 0 (.nodeCall ⟨emptyValue (SourceEqualityOriginalAllocationPreparation.prepare
        (SourceEqualityConstraintOrigins.guards expression) initial).2, value⟩
        (caller width (SourceEqualityOriginalAllocationPreparation.prepare
          (SourceEqualityConstraintOrigins.guards expression) initial).2 heap))) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        ∃ result after next final,
          SourceCurrentAllocatedPartialWorkerCompletion.StableRun
            (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n 0
              ⟨emptyValue cache, value⟩ (caller width cache heap)) result after ∧
          ∃ actual : NodeCall 0 ⟨emptyValue cache, value⟩ (caller width cache heap) result after,
            NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
            Post formulas solver next (caller width cache heap) after final ∧
            Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow value result ∧ result.free = [] ∧
            ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨fields, prepared, value, heap, built, result, after, next, final, stable, actual, reads, checks, post, available, stored, bounded, language⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterRoot.prepared_root width initial valid expression domain cached formulas solver 0 ranges
  have closed := SourceCurrentAllocatedFiniteOrdinaryFinite.closed after.checked.native.machine.heap
    post.context.ready.semantic.ready.semantic.1.normal.facts.coherent result available bounded.1
  exact ⟨fields, prepared, value, heap, built, result, after, next, final, stable, actual, reads, checks, post, available, stored,
    bounded, closed, language⟩

#print axioms prepared_zero_budget
#check @prepared_zero_budget
end FiniteOrdinaryRootIndependentChecks
