import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentAllocatedPartialWorkerActual
import MicroCFTA.SourceEqualityOriginalAllocationPreparation

/-!
# Root reduction after covered original construction

Construction and allocation history derive the initial caller context.
The root uses the empty equality value from the actual returned interner.
A successful literal worker then derives its own complete semantic receipt.
Reached machine checks and successful execution remain explicit premises.
These theorems do not establish general termination or host cache behavior.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConstructedRoot
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Covered construction discharges every initial semantic and cache premise of the literal root theorem. -/
theorem constructed_root
    (width : Nat) {initialCache finalCache : Cache.State Key} {originals : List Guard}
    (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Node) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {fuel g s r e p h m c n budget : Nat} {result : Node} {after : Caller width}
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget
      ⟨emptyValue finalCache, value⟩ (caller width finalCache heap))
    (done : nodeCall fuel g s r e p h m c n budget
      ⟨emptyValue finalCache, value⟩ (caller width finalCache heap) = .done result after) :
    ∃ next final, ∃ actual : NodeCall budget ⟨emptyValue finalCache, value⟩
      (caller width finalCache heap) result after,
      NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next (caller width finalCache heap) after final ∧
      Available after.checked.native.machine.heap result ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨context, identity, same, ready, available, _, _⟩ :=
    SourceCurrentAllocatedPartialInitialization.constructed width history valid expression covered value heap built formulas solver
  have literalRanges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget
      ⟨.live identity [], value⟩ (caller width finalCache heap) := by
    simpa only [same] using ranges
  have literalDone : nodeCall fuel g s r e p h m c n budget
      ⟨.live identity [], value⟩ (caller width finalCache heap) = .done result after := by
    simpa only [same] using done
  have actual := SourceCurrentAllocatedPartialWorkerActual.root_exact formulas solver context ready available literalRanges literalDone
  simpa only [same] using actual

/-- Normalized literal fields derive their own allocation history before exact successful root reduction. -/
theorem prepared_root
    (width : Nat) (initialCache : Cache.State Key) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (value : Node) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {fuel g s r e p h m c n budget : Nat} {result : Node} {after : Caller width}
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall fuel g s r e p h m c n budget
      ⟨emptyValue (SourceEqualityOriginalAllocationPreparation.prepare
        (SourceEqualityConstraintOrigins.guards expression) initialCache).2, value⟩
      (caller width (SourceEqualityOriginalAllocationPreparation.prepare
        (SourceEqualityConstraintOrigins.guards expression) initialCache).2 heap))
    (done : nodeCall fuel g s r e p h m c n budget
      ⟨emptyValue (SourceEqualityOriginalAllocationPreparation.prepare
        (SourceEqualityConstraintOrigins.guards expression) initialCache).2, value⟩
      (caller width (SourceEqualityOriginalAllocationPreparation.prepare
        (SourceEqualityConstraintOrigins.guards expression) initialCache).2 heap) = .done result after) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initialCache).2
    ∃ fields, SourceEqualityOriginalAllocationPreparation.Receipt
      (SourceEqualityConstraintOrigins.guards expression) initialCache fields cache ∧
      ∃ next final, ∃ actual : NodeCall budget ⟨emptyValue cache, value⟩
        (caller width cache heap) result after,
        NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next (caller width cache heap) after final ∧
        Available after.checked.native.machine.heap result ∧
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
  exact ⟨fields, receipt, constructed_root width receipt.history valid expression
    (fun _ member => member) value heap built formulas solver ranges done⟩

end MicroCFTA.SourceCurrentAllocatedPartialConstructedRoot
