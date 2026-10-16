import MicroCFTA.SourceCurrentAllocatedPartialPlainNode
import MicroCFTA.SourceCurrentAllocatedPartialConstructedRoot

/-!
# Constructed plain root execution without a worker-success premise

Covered construction derives the cold caller and actual empty inherited
identity. The Region theorem constructs finite literal node execution.
The same return preserves the full guarded language. Field preparation
can derive its own allocation history. Construction success and Region
remain explicit inputs. General constrained completion remains separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialPlainRoot
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialGraph (NodeCall)
open SourceCurrentAllocatedPartialSourceReads (NodeCallReads)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Covered construction and Region derive stable root completion and exact full-language preservation. -/
theorem constructed_root
    (width : Nat) {initialCache finalCache : Cache.State Key} {originals : List Guard}
    (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Node) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (region : SourceEqualityPartialPlainRegion.Region value)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
          ⟨emptyValue finalCache, value⟩ (caller width finalCache heap)) result after ∧
      ∃ actual : NodeCall budget ⟨emptyValue finalCache, value⟩ (caller width finalCache heap) result after,
        NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next (caller width finalCache heap) after final ∧
        Available after.checked.native.machine.heap result ∧ Stored after ∧
        ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨context, identity, same, ready, available, _closed, _original⟩ :=
    SourceCurrentAllocatedPartialInitialization.constructed width history valid expression covered value heap built formulas solver
  have inherited : SourceEqualityConstraintAllocation.Ready
      (caller width finalCache heap).checked.operations.constraints (emptyValue finalCache) := by
    rw [same]
    exact ready
  have stored : Stored (caller width finalCache heap) := SourceCurrentAllocatedPartialReturnedDomain.initial _ _ _
  have active : SourceCurrentAllocatedPartialActiveOrder.ActiveAbove
      (SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨emptyValue finalCache, value⟩) (caller width finalCache heap) :=
    SourceCurrentAllocatedPartialActiveOrder.initial_above _ _ _ _
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, law⟩ :=
    SourceCurrentAllocatedPartialPlainNode.finite formulas solver budget ⟨emptyValue finalCache, value⟩
      context inherited available region stored active
  refine ⟨result, after, next, final, stable, actual, reads, checks, post, output, retained, ?_⟩
  intro ambient term
  apply (law ambient term).2
  simp [same, SourceEqualityConstraintAllocation.Value.payload, SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]

/-- Actual field preparation derives the history used by finite exact plain root execution. -/
theorem prepared_root
    (width : Nat) (initialCache : Cache.State Key) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (value : Node) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (region : SourceEqualityPartialPlainRegion.Region value)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initialCache).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initialCache fields cache ∧
      ∃ result after next final,
        SourceCurrentAllocatedPartialWorkerCompletion.StableRun
          (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
            ⟨emptyValue cache, value⟩ (caller width cache heap)) result after ∧
        ∃ actual : NodeCall budget ⟨emptyValue cache, value⟩ (caller width cache heap) result after,
          NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
          Post formulas solver next (caller width cache heap) after final ∧
          Available after.checked.native.machine.heap result ∧ Stored after ∧
          ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  let cache := (SourceEqualityOriginalAllocationPreparation.prepare
    (SourceEqualityConstraintOrigins.guards expression) initialCache).2
  obtain ⟨fields, finalCache, prepared⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete
    (SourceEqualityConstraintOrigins.guards expression) initialCache valid cached
  have sameCache : cache = finalCache := congrArg Prod.snd prepared.done
  have receipt : SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initialCache fields cache := by
    simpa only [sameCache] using prepared
  exact ⟨fields, receipt, constructed_root width receipt.history valid expression (fun _ member => member)
    value heap built region formulas solver budget⟩

end MicroCFTA.SourceCurrentAllocatedPartialPlainRoot
