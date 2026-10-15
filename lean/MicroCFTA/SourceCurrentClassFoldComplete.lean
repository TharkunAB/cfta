import MicroCFTA.SourceCurrentClassFoldDomains
import MicroCFTA.SourceCurrentClassEditComplete

/-!
# Finite current class folds from actual local range plans

Every tail completes before the next head captures its returned forest.
Path-domain preservation derives each next capture premise. Actual native
word checks remain at the reached prefixes. The completed fold and final
propagation derive stable execution of the existing literal workers.
-/
namespace MicroCFTA.SourceCurrentClassFoldComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open SourceEqualityProjectionPathDomain SourceCurrentClassFoldDomains

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- Actual reached class range plans derive finite right-fold execution and every tracked path domain. -/
theorem fold_complete {records values} {before : NativeState width Symbol Guard}
    (ranges : Ranges emptyGuard conjoin clear top records values before)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    ∃ results after, Fold emptyGuard conjoin clear top records values before results after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      (∀ path : List Int, ForestClosed path values → ForestClosed path results) ∧
      SourceEqualityClassFoldWorkerProofs.StableRun
        (fun e p h c n => SourceEqualityClassFoldWorker.fold emptyGuard conjoin clear top e p h c n records values before) results after := by
  induction ranges with
  | nil =>
      exact ⟨_, _, .nil, ready, pure_keeps _ ready.semantic.ready, available, (fun _ domain => domain),
        SourceEqualityClassFoldWorkerProofs.fold_stable emptyGuard conjoin clear top .nil⟩
  | @cons records values before record tail head ih =>
      obtain ⟨middle, next, first, nextReady, firstKeeps, firstAvailable, firstDomains, _⟩ :=
        ih (fun own member => coherent own (List.mem_cons_of_mem _ member))
          (fun own member => active own (List.mem_cons_of_mem _ member)) ready available
          (fun own member => domains own (List.mem_cons_of_mem _ member))
      obtain ⟨results, after, last, finalReady, lastKeeps, resultAvailable, resultDomains, _⟩ :=
        SourceCurrentClassEditComplete.class_complete emptyGuard conjoin clear top record
          (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) middle next
          (head middle next first) nextReady firstAvailable
          (fun path member => firstDomains _ (domains _ List.mem_cons_self path member))
      have trace : Fold emptyGuard conjoin clear top (record :: records) values before results after := .cons first last
      exact ⟨results, after, trace, finalReady, firstKeeps.trans lastKeeps, resultAvailable,
        (fun path domain => resultDomains path (firstDomains path domain)),
        SourceEqualityClassFoldWorkerProofs.fold_stable emptyGuard conjoin clear top trace⟩

/-- Finite source range plans derive final propagation and stable literal pass execution. -/
theorem pass_complete {records values} {before : NativeState width Symbol Guard}
    (ranges : Ranges emptyGuard conjoin clear top records values before)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    ∃ results after, Pass emptyGuard conjoin clear top records values before results after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      (∀ path : List Int, ForestClosed path values → ForestClosed path results) ∧
      SourceEqualityClassFoldWorkerProofs.StableRun
        (fun e p h c n => SourceEqualityClassFoldWorker.pass emptyGuard conjoin clear top e p h c n records values before) results after := by
  obtain ⟨results, after, fold, finalReady, kept, available, preserved, _⟩ :=
    fold_complete emptyGuard conjoin clear top ranges coherent active ready available domains
  have trace : Pass emptyGuard conjoin clear top records values before (EqualityLeafProjectionRuntimeEmpty.propagate results) after := .done fold
  exact ⟨_, after, trace, finalReady, kept, propagate_available _ _ available,
    (fun path domain => propagate_domains _ path (preserved path domain)),
    SourceEqualityClassFoldWorkerProofs.pass_stable emptyGuard conjoin clear top trace⟩

end MicroCFTA.SourceCurrentClassFoldComplete
