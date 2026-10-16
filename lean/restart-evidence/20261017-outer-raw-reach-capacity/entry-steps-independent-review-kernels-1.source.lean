import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRoot

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.OuterEntryResourceReview
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Entry Reach)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs (Admitted)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot (initialNodes initialEdges)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryActualOuterWork (WorkBounds)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (NodeCertificate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "Syntax" => InternedNestedConstruction.Syntax Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- The plans quantify over the original raw Reach relation and all its completed-prefix choices. -/
def AllRawPlans (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (budget : Nat) (root : Entry (bits + 2)) : Prop :=
  SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan bits budget root ∧
  SourceCurrentAllocatedFiniteOrdinaryOuterEntries.Plan budget root ∧
  ∀ entry, Reach budget root entry → Admitted bits formulas solver entry

/-- Original source syntax and initial headroom derive admission on every raw reached entry. -/
theorem constructed_source_full_raw_plans
    (bits : Nat) {initial cache : Cache.State Key} {originals : List Guard}
    (history : History initial cache originals) (valid : Cache.Valid initial)
    (expression : Syntax) (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (room : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Headroom bits heap (initialNodes value) (initialEdges value)) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Admitted bits formulas solver (.nodeCall ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) ∧
      AllRawPlans bits formulas solver budget (.nodeCall ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) := by
  obtain ⟨value, heap, built, context, _base, valueDomain, identity, same, inherited, available, _free, _original⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.constructed (bits + 2) history valid expression domain covered formulas solver
  have ready : SourceEqualityConstraintAllocation.Ready
      (caller (bits + 2) cache heap).checked.operations.constraints (emptyValue cache) := by rw [same]; exact inherited
  have stored := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState.caller_stored (bits + 2) cache heap
  have active := SourceCurrentAllocatedPartialActiveOrder.initial_above (width := bits + 2)
    (SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨emptyValue cache, value⟩)
    (checked (bits + 2) cache heap) SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
  have admitted := SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs.node_call formulas solver
    (inventory expression value heap built) ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)
    (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.limits value).1
    (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.limits value).2
    (MergedOrdinaryHeight.height value) (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.limits value)
    context stored ready available valueDomain
    (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.node_shape_self value valueDomain)
    (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.node_self value valueDomain) (Nat.le_refl _)
    (room value heap built) active
  exact ⟨value, heap, built, admitted,
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach.numeric_plan bits formulas solver admitted,
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach.ranges bits formulas solver admitted,
    fun entry reached => SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach.reach bits formulas solver reached admitted⟩

/-- Literal source-field preparation derives the same universal raw plans without a caller Plan premise. -/
theorem prepared_source_full_raw_plans
    (bits : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : Syntax) (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, SourceEqualityGuardReadback.Cached original.equalities)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (room : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Headroom bits heap (initialNodes value) (initialEdges value)) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        Admitted bits formulas solver (.nodeCall ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) ∧
        AllRawPlans bits formulas solver budget (.nodeCall ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) := by
  let cache := (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2
  obtain ⟨fields, finalCache, receipt⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete
    (SourceEqualityConstraintOrigins.guards expression) initial valid cached
  have same : cache = finalCache := congrArg Prod.snd receipt.done
  have exactReceipt : SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initial fields cache := by simpa only [same] using receipt
  exact ⟨fields, exactReceipt, constructed_source_full_raw_plans bits exactReceipt.history valid expression domain
    (fun _ member => member) formulas solver budget room⟩

/-- The older Plan-based root now constructs its own return from initial headroom alone. -/
theorem old_root_from_initial_resources
    (bits : Nat) {initial cache : Cache.State Key} {originals : List Guard}
    (history : History initial cache originals) (valid : Cache.Valid initial)
    (expression : Syntax) (domain : SourceCurrentAllocatedFiniteOrdinaryConstruction.Node expression)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat)
    (room : ∀ value heap, InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap →
      Headroom bits heap (initialNodes value) (initialEdges value)) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      AllRawPlans bits formulas solver budget (.nodeCall ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) ∧
      ∃ result after next final,
        SourceCurrentAllocatedPartialWorkerCompletion.StableRun
          (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
            ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap)) result after ∧
        ∃ actual : NodeCall budget ⟨emptyValue cache, value⟩ (caller (bits + 2) cache heap) result after,
          NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
          Post formulas solver next (caller (bits + 2) cache heap) after final ∧ Stored after ∧
          NodeCertificate ⟨emptyValue cache, value⟩ result ∧
          WorkBounds heap after.checked.native.machine.heap (initialNodes value) (initialEdges value) ∧
          Headroom bits after.checked.native.machine.heap 0 0 ∧
          (∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term) := by
  obtain ⟨value, heap, built, _admitted, plans⟩ := constructed_source_full_raw_plans bits history valid
    expression domain covered formulas solver budget room
  have ranges : ∀ other otherHeap,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done other otherHeap →
      SourceCurrentAllocatedFiniteOrdinaryOuterEntries.Plan budget
        (.nodeCall ⟨emptyValue cache, other⟩ (caller (bits + 2) cache otherHeap)) := by
    intro other otherHeap otherBuilt
    obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj (built.symm.trans otherBuilt)
    exact plans.2.1
  obtain ⟨other, otherHeap, otherBuilt, result, after, next, final, stable, actual, reads, checks, post,
      _available, _base, _narrow, language⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterRoot.constructed_root (bits + 2) history valid expression domain
      covered formulas solver budget ranges
  obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj (built.symm.trans otherBuilt)
  obtain ⟨sourceValue, sourceHeap, sourceBuilt, context, _base, valueDomain,
      identity, same, inheritedReady, available, _free, _original⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterInitial.constructed (bits + 2) history valid expression domain covered formulas solver
  obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj (built.symm.trans sourceBuilt)
  have initialStored := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState.caller_stored (bits + 2) cache heap
  have inherited : SourceEqualityConstraintAllocation.Ready
      (caller (bits + 2) cache heap).checked.operations.constraints (emptyValue cache) := by rw [same]; exact inheritedReady
  have produced := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.node_call formulas solver reads (inventory expression value heap built)
    context inherited available valueDomain initialStored
  have work := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.node_call formulas solver reads (inventory expression value heap built)
    context inherited available valueDomain initialStored
    (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.limits value).1
    (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.limits value).2
    (MergedOrdinaryHeight.height value) (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.limits value)
    (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.node_shape_self value valueDomain)
    (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.node_self value valueDomain) (Nat.le_refl _)
  have finalRoom : Headroom bits after.checked.native.machine.heap 0 0 :=
    ((room value heap built).mono (by omega) (by omega)).after work
  exact ⟨value, heap, built, plans, result, after, next, final, stable, actual, reads, checks,
    post, produced.1, produced.2.2, work, finalRoom, language⟩

#print axioms AllRawPlans
#check @AllRawPlans
#print axioms constructed_source_full_raw_plans
#check @constructed_source_full_raw_plans
#print axioms prepared_source_full_raw_plans
#check @prepared_source_full_raw_plans
#print axioms old_root_from_initial_resources
#check @old_root_from_initial_resources
end MicroCFTA.OuterEntryResourceReview
