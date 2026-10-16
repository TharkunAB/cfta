import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeRoot
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterInitial

/-!
# Initial resources discharge the original ordinary root Plan

The invariant follows the complete original raw Reach relation.
Each reached parent obtains capacity before that parent executes.
The derived Plan enters the preserved conditional root theorem.
The same return retains the complete earlier resource and language laws.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryRoot
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
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers (nodeNodes nodeEdges)
open SourceCurrentAllocatedFiniteOrdinaryActualOuterWork (WorkBounds)

open SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot (initialNodes initialEdges)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Initial profiles and headroom derive finite root execution and its actual request bounds. -/
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
    (rows arity bound : Nat) (limits : SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits)
    (profile : SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape rows arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits request.value)
    (heightBound : MergedOrdinaryHeight.height request.value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound)) :
    SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan bits budget (.nodeCall request before) ∧
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : NodeCall budget request before result after,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
        Stored after ∧ NodeNarrow request.value result ∧ NodeCertificate request result ∧
        WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
          (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound) ∧
        Headroom bits after.checked.native.machine.heap 0 0 ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result := by
  have admitted := SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs.node_call formulas solver inventory
    request before rows arity bound limits initial stored inherited available domain profile guards heightBound room active
  have plan := SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach.numeric_plan bits formulas solver (budget := budget) admitted
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, narrowed, quantitative, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeRoot.finite bits formulas solver budget request
      initial inherited available domain stored active plan
  have work := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.node_call formulas solver reads inventory
    initial inherited available domain stored rows arity bound limits profile guards heightBound
  have finalRoom : Headroom bits after.checked.native.machine.heap 0 0 :=
    (room.mono (by omega) (by omega)).after work
  exact ⟨plan, result, after, next, final, stable, actual, reads, checks, post, output,
    retained, narrowed, quantitative, work, finalRoom, law⟩

/-- Source syntax and initial constructor supply derive stable root execution and exact full-language preservation. -/
theorem constructed_root
    (bits : Nat) {initial finalCache : Cache.State Key} {originals : List Guard}
    (history : History initial finalCache originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (capacity : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Headroom bits heap (initialNodes value) (initialEdges value)) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan bits budget
        (.nodeCall ⟨emptyValue finalCache, value⟩ (caller (bits + 2) finalCache heap)) ∧
      ∃ result after next final,
        SourceCurrentAllocatedPartialWorkerCompletion.StableRun
          (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
            ⟨emptyValue finalCache, value⟩ (caller (bits + 2) finalCache heap)) result after ∧
        ∃ actual : NodeCall budget ⟨emptyValue finalCache, value⟩ (caller (bits + 2) finalCache heap) result after,
          NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
          Post formulas solver next (caller (bits + 2) finalCache heap) after final ∧
          Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow value result ∧
          NodeCertificate ⟨emptyValue finalCache, value⟩ result ∧
          WorkBounds heap after.checked.native.machine.heap (initialNodes value) (initialEdges value) ∧
          Headroom bits after.checked.native.machine.heap 0 0 ∧ ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨value, heap, built, context, _stored, resultDomain, identity, same, ready, available, _free, _original⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.constructed (bits + 2) history valid expression domain covered formulas solver
  have strong := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState.caller_stored (bits + 2) finalCache heap
  have inherited : SourceEqualityConstraintAllocation.Ready
      (caller (bits + 2) finalCache heap).checked.operations.constraints (emptyValue finalCache) := by rw [same]; exact ready
  have active := SourceCurrentAllocatedPartialActiveOrder.initial_above (width := bits + 2)
    (SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨emptyValue finalCache, value⟩)
    (checked (bits + 2) finalCache heap) SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  obtain ⟨plan, result, after, next, final, stable, actual, reads, checks, post, output, retained, narrowed, quantitative, work, finalRoom, law⟩ :=
    finite bits formulas solver budget ⟨emptyValue finalCache, value⟩
      context inherited available resultDomain strong active
      (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.limits value).1
      (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.limits value).2
      (MergedOrdinaryHeight.height value) (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.limits value)
      (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.node_shape_self value resultDomain)
      (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.node_self value resultDomain) (Nat.le_refl _)
      (capacity value heap built)
  refine ⟨value, heap, built, plan, result, after, next, final, stable, actual, reads, checks, post, output, retained, narrowed, quantitative, work, finalRoom, ?_⟩
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
      Headroom bits heap (initialNodes value) (initialEdges value)) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan bits budget
          (.nodeCall ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) ∧
        ∃ result after next final,
          SourceCurrentAllocatedPartialWorkerCompletion.StableRun
            (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
              ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) result after ∧
          ∃ actual : NodeCall budget ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap) result after,
            NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
            Post formulas solver next (caller (bits + 2) cache heap) after final ∧
            Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow value result ∧ NodeCertificate ⟨emptyValue cache, value⟩ result ∧
            WorkBounds heap after.checked.native.machine.heap (initialNodes value) (initialEdges value) ∧
            Headroom bits after.checked.native.machine.heap 0 0 ∧
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


end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryRoot
