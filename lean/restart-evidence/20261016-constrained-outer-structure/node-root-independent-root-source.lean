import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterInitial

/-!
# Constructed finite ordinary root reduction

Source construction derives its own complete root and initial context.
Strong rank induction constructs the actual recursive caller return.
The same return preserves the complete guarded language.
The public range plan checks independently reached parent entries.
Its quantitative machine capacity bound remains an explicit obligation.
This result covers one finite ordinary pass, not general Mu execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRoot
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
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

/-- Source syntax and entry range checks derive stable literal root execution and exact full-language preservation. -/
theorem constructed_root
    (width : Nat) {initial finalCache : Cache.State Key} {originals : List Guard}
    (history : History initial finalCache originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (ranges : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Plan budget (.nodeCall ⟨emptyValue finalCache, value⟩ (caller width finalCache heap))) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      ∃ result after next final,
        SourceCurrentAllocatedPartialWorkerCompletion.StableRun
          (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
            ⟨emptyValue finalCache, value⟩ (caller width finalCache heap)) result after ∧
        ∃ actual : NodeCall budget ⟨emptyValue finalCache, value⟩ (caller width finalCache heap) result after,
          NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
          Post formulas solver next (caller width finalCache heap) after final ∧
          Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow value result ∧
          ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨value, heap, built, context, stored, resultDomain, identity, same, ready, available, _free, _original⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.constructed width history valid expression domain covered formulas solver
  have inherited : SourceEqualityConstraintAllocation.Ready
      (caller width finalCache heap).checked.operations.constraints (emptyValue finalCache) := by rw [same]; exact ready
  have active := SourceCurrentAllocatedPartialActiveOrder.initial_above (width := width)
    (SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨emptyValue finalCache, value⟩)
    (checked width finalCache heap) SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, narrowed, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterNode.finite formulas solver budget ⟨emptyValue finalCache, value⟩
      context inherited available resultDomain stored active (ranges value heap built)
  refine ⟨value, heap, built, result, after, next, final, stable, actual, reads, checks, post, output, retained, narrowed, ?_⟩
  intro ambient term
  apply (law ambient term).2
  simp [same, SourceEqualityConstraintAllocation.Value.payload, SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]

/-- Actual field preparation supplies history before finite ordinary root construction and reduction. -/
theorem prepared_root
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (ranges : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Plan budget (.nodeCall ⟨emptyValue (SourceEqualityOriginalAllocationPreparation.prepare
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
            (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
              ⟨emptyValue cache, value⟩ (caller width cache heap)) result after ∧
          ∃ actual : NodeCall budget ⟨emptyValue cache, value⟩ (caller width cache heap) result after,
            NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
            Post formulas solver next (caller width cache heap) after final ∧
            Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow value result ∧
            ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  let cache := (SourceEqualityOriginalAllocationPreparation.prepare
    (SourceEqualityConstraintOrigins.guards expression) initial).2
  obtain ⟨fields, finalCache, receipt⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete
    (SourceEqualityConstraintOrigins.guards expression) initial valid cached
  have same : cache = finalCache := congrArg Prod.snd receipt.done
  have actual : SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache := by simpa only [same] using receipt
  exact ⟨fields, actual, constructed_root width actual.history valid expression domain
    (fun _ member => member) formulas solver budget ranges⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRoot
