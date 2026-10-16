import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterInitial
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterAdmission
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryInitialCapacity

/-!
# Numeric capacity for constructed ordinary root reduction

Source construction derives its own complete root and initial context.
Strong rank induction constructs the actual recursive caller return.
The same return preserves the complete guarded language.
Reach admission derives each state invariant before its parent runs.
The public plan contains numeric capacity at those reached entries.
A total reduction allocation bound remains a separate obligation.
This result covers one finite ordinary pass, not general Mu execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNumericRoot
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
local notation "Plan" => SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Admission at all reached entries derives finite root execution from numeric parent capacity. -/
theorem finite (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {before : SourceCurrentAllocatedPartialState.State (bits + 2)} {memos : EndpointMemoGateTrace.Memos}
    (budget : Nat) (request : NodeRequest)
    (initial : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node request.value)
    (stored : Stored before)
    (active : SourceCurrentAllocatedPartialActiveOrder.ActiveAbove
      (SourceCurrentAllocatedPartialActiveOrder.nodeRank request) before)
    (plan : Plan bits budget (.nodeCall request before)) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : NodeCall budget request before result after,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ NodeNarrow request.value result ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result := by
  have admitted : SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Admitted formulas solver (.nodeCall request before) :=
    ⟨inventory, memos, initial, stored, inherited, available, domain⟩
  have ranges := SourceCurrentAllocatedFiniteOrdinaryOuterAdmission.ranges bits formulas solver admitted plan
  exact SourceCurrentAllocatedFiniteOrdinaryOuterNode.finite formulas solver budget request initial inherited available domain
    stored active ranges

/-- Source syntax and numeric parent capacity derive stable literal root execution and exact full-language preservation. -/
theorem constructed_root
    (bits : Nat) {initial finalCache : Cache.State Key} {originals : List Guard}
    (history : History initial finalCache originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (capacity : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Plan bits budget (.nodeCall ⟨emptyValue finalCache, value⟩ (caller (bits + 2) finalCache heap))) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      ∃ result after next final,
        SourceCurrentAllocatedPartialWorkerCompletion.StableRun
          (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
            ⟨emptyValue finalCache, value⟩ (caller (bits + 2) finalCache heap)) result after ∧
        ∃ actual : NodeCall budget ⟨emptyValue finalCache, value⟩ (caller (bits + 2) finalCache heap) result after,
          NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
          Post formulas solver next (caller (bits + 2) finalCache heap) after final ∧
          Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow value result ∧
          ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨value, heap, built, context, stored, resultDomain, identity, same, ready, available, _free, _original⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.constructed (bits + 2) history valid expression domain covered formulas solver
  have inherited : SourceEqualityConstraintAllocation.Ready
      (caller (bits + 2) finalCache heap).checked.operations.constraints (emptyValue finalCache) := by rw [same]; exact ready
  have active := SourceCurrentAllocatedPartialActiveOrder.initial_above (width := bits + 2)
    (SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨emptyValue finalCache, value⟩)
    (checked (bits + 2) finalCache heap) SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, narrowed, law⟩ :=
    finite bits formulas solver budget ⟨emptyValue finalCache, value⟩
      context inherited available resultDomain stored active (capacity value heap built)
  refine ⟨value, heap, built, result, after, next, final, stable, actual, reads, checks, post, output, retained, narrowed, ?_⟩
  intro ambient term
  apply (law ambient term).2
  simp [same, SourceEqualityConstraintAllocation.Value.payload, SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]

/-- Actual field preparation supplies history before finite ordinary root construction and reduction. -/
theorem prepared_root
    (bits : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (capacity : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Plan bits budget (.nodeCall ⟨emptyValue (SourceEqualityOriginalAllocationPreparation.prepare
        (SourceEqualityConstraintOrigins.guards expression) initial).2, value⟩
        (caller (bits + 2) (SourceEqualityOriginalAllocationPreparation.prepare
          (SourceEqualityConstraintOrigins.guards expression) initial).2 heap))) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        ∃ result after next final,
          SourceCurrentAllocatedPartialWorkerCompletion.StableRun
            (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
              ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) result after ∧
          ∃ actual : NodeCall budget ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap) result after,
            NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
            Post formulas solver next (caller (bits + 2) cache heap) after final ∧
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
  exact ⟨fields, actual, constructed_root bits actual.history valid expression domain
    (fun _ member => member) formulas solver budget capacity⟩

/-- Static syntax bounds supply initial capacity beside the complete numeric-plan root execution. -/
theorem bounded_prepared_root
    (bits : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (nodes : SourceCurrentAllocatedFiniteOrdinaryConstructionReservations.nodeCount expression ≤ 2 ^ bits)
    (edges : SourceCurrentAllocatedFiniteOrdinaryConstructionReservations.edgeCount expression ≤ 2 ^ (bits + 2))
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (capacity : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
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
        ∃ result after next final,
          SourceCurrentAllocatedPartialWorkerCompletion.StableRun
            (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
              ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) result after ∧
          ∃ actual : NodeCall budget ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap) result after,
            NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
            Post formulas solver next (caller (bits + 2) cache heap) after final ∧
            Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow value result ∧
            ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨fields, fieldReceipt, value, heap, built, execution⟩ :=
    prepared_root bits initial valid expression domain cached formulas solver budget capacity
  exact ⟨fields, fieldReceipt, value, heap, built,
    SourceCurrentAllocatedFiniteOrdinaryInitialCapacity.built_capacity bits _ expression domain value heap built nodes edges,
    execution⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNumericRoot
