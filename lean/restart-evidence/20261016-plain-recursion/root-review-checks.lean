import MicroCFTA.SourceCurrentAllocatedPartialPlainRoot

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainRoot.constructed_root
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainRoot.constructed_root
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainRoot.prepared_root
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainRoot.prepared_root

namespace RootReviewChecks
open MicroCFTA
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialGraph (NodeCall)
open SourceCurrentAllocatedPartialSourceReads (NodeCallReads)
open SourceCurrentAllocatedPartialChecks (Checks nodeCallTrace)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedPartialReturnedDomain (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

theorem covered_actual_zero_budget
    (width : Nat) {initialCache finalCache : Cache.State Key} {originals : List Guard}
    (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Node) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (region : SourceEqualityPartialPlainRegion.Region value)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ f g s r e p h m c n result after next final,
      SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n 0
        ⟨emptyValue finalCache, value⟩ (caller width finalCache heap) = .done result after ∧
      ∃ actual : NodeCall 0 ⟨emptyValue finalCache, value⟩ (caller width finalCache heap) result after,
        NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next (caller width finalCache heap) after final ∧
        Available after.checked.native.machine.heap result ∧ Stored after ∧
        ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨result, after, next, final, ⟨f, g, s, r, e, p, h, m, c, n, stable⟩,
    actual, reads, checks, post, available, stored, language⟩ :=
    SourceCurrentAllocatedPartialPlainRoot.constructed_root width history valid expression covered value heap built region
      formulas solver 0
  exact ⟨f, g, s, r, e, p, h, m, c, n, result, after, next, final,
    stable f g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _),
    actual, reads, checks, post, available, stored, language⟩

theorem prepared_retains_caller_interner
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
      Cache.Extends initialCache.table cache.table ∧
      ∃ result after next final,
        SourceCurrentAllocatedPartialWorkerCompletion.StableRun
          (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
            ⟨emptyValue cache, value⟩ (caller width cache heap)) result after ∧
        Post formulas solver next (caller width cache heap) after final ∧ Stored after ∧
        ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨fields, receipt, result, after, next, final, stable, actual, reads, checks, post, available, stored, language⟩ :=
    SourceCurrentAllocatedPartialPlainRoot.prepared_root width initialCache valid expression cached value heap built region
      formulas solver budget
  exact ⟨fields, receipt, receipt.retained, result, after, next, final, stable, post, stored, language⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
theorem actual_nonzero_empty_identity :
    ∃ cache : Cache.State Key, Cache.Valid cache ∧ emptyValue cache = .live 7 [] ∧
      SourceEqualityConstraintAllocation.Ready (operations cache).constraints (.live 7 []) := by
  let cache : Cache.State Key :=
    ⟨8, fun identity => if identity = 7 then some (SourceEqualityPartialConstraintKey.key []) else none,
      fun key => if key = SourceEqualityPartialConstraintKey.key [] then
        some ⟨7, SourceEqualityPartialConstraintKey.key []⟩ else none⟩
  have valid : Cache.Valid cache := by
    constructor
    · intro identity key issued
      by_cases same : identity = 7
      · subst identity
        change 7 < 8
        decide
      · simp [cache, same] at issued
    · intro key value found
      by_cases same : key = SourceEqualityPartialConstraintKey.key []
      · subst key
        simp only [cache, ↓reduceIte] at found
        cases found
        exact ⟨rfl, by simp only [cache, ↓reduceIte]⟩
      · simp [cache, same] at found
  have identity : emptyValue cache = .live 7 [] := by
    simp only [emptyValue, SourceEqualityConstraintAllocation.intern, Cache.intern, cache, ↓reduceIte]
  refine ⟨cache, valid, identity, ?_⟩
  rw [← identity]
  exact (operations_correct cache valid).2.2

theorem constructed_empty_needs_no_caller_or_range_premise
    (width : Nat) (cache : Cache.State Key) (valid : Cache.Valid cache)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n 0
          ⟨emptyValue cache, .empty⟩ (caller width cache empty)) result after ∧
      ∃ actual : NodeCall 0 ⟨emptyValue cache, .empty⟩ (caller width cache empty) result after,
        NodeCallReads formulas solver actual globals final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next (caller width cache empty) after final ∧
        Available after.checked.native.machine.heap result ∧ Stored after ∧
        ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient .empty term := by
  exact SourceCurrentAllocatedPartialPlainRoot.constructed_root width (History.start cache) valid .empty
    (by intro original absent; cases absent) .empty empty
    (by simp only [InternedFreshOrdinaryConstruction.build]) .empty formulas solver 0

end RootReviewChecks

#print axioms RootReviewChecks.covered_actual_zero_budget
#check @RootReviewChecks.covered_actual_zero_budget
#print axioms RootReviewChecks.prepared_retains_caller_interner
#check @RootReviewChecks.prepared_retains_caller_interner
#print axioms RootReviewChecks.actual_nonzero_empty_identity
#check @RootReviewChecks.actual_nonzero_empty_identity
#print axioms RootReviewChecks.constructed_empty_needs_no_caller_or_range_premise
#check @RootReviewChecks.constructed_empty_needs_no_caller_or_range_premise
