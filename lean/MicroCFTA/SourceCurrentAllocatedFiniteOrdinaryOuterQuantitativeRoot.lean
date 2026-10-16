import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterGuardRoot

/-!
# Quantitative certificates at the same constructed ordinary root return

The existing numeric Plan constructs the actual root execution.
The quantitative producer follows those same actual reads.
The return retains the complete earlier stores and a universal output law.
The numeric Plan remains an explicit input. Initial headroom remains open.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeRoot
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialGraph (NodeCall)
open SourceCurrentAllocatedPartialSourceReads (NodeCallReads)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (NodeCertificate)
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
        Stored after ∧ NodeNarrow request.value result ∧ NodeCertificate request result ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result := by
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, _stored, _narrowed, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterGuardRoot.finite bits formulas solver budget request
      initial inherited available domain stored.base active plan
  have retained := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.node_call formulas solver reads inventory
    initial inherited available domain stored
  exact ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained.1, retained.2.1, retained.2.2, law⟩

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
          NodeCertificate ⟨emptyValue finalCache, value⟩ result ∧ ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨value, heap, built, context, _stored, resultDomain, identity, same, ready, available, _free, _original⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.constructed (bits + 2) history valid expression domain covered formulas solver
  have strong := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState.caller_stored (bits + 2) finalCache heap
  have inherited : SourceEqualityConstraintAllocation.Ready
      (caller (bits + 2) finalCache heap).checked.operations.constraints (emptyValue finalCache) := by rw [same]; exact ready
  have active := SourceCurrentAllocatedPartialActiveOrder.initial_above (width := bits + 2)
    (SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨emptyValue finalCache, value⟩)
    (checked (bits + 2) finalCache heap) SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, narrowed, quantitative, law⟩ :=
    finite bits formulas solver budget ⟨emptyValue finalCache, value⟩
      context inherited available resultDomain strong active (capacity value heap built)
  refine ⟨value, heap, built, result, after, next, final, stable, actual, reads, checks, post, output, retained, narrowed, quantitative, ?_⟩
  intro ambient term
  apply (law ambient term).2
  simp [same, SourceEqualityConstraintAllocation.Value.payload, SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeRoot
