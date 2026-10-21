import MicroCFTA.SourceCurrentClassEditDomains
import MicroCFTA.SourceEqualityClassFoldWorkerProofs

/-!
# Selected path domains through the actual class right fold

Each head class captures the forest returned by the completed tail.
Tail preservation derives the domains for that actual class capture.
The full fold retains every tracked signed path domain. Final literal
empty propagation preserves those domains in the same returned heap.
-/
namespace MicroCFTA.SourceCurrentClassFoldDomains
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open SourceEqualityProjectionPathDomain SourceCurrentEditDomains

/-- Final literal empty propagation retains available values without a forest closedness premise. -/
theorem propagate_available (heap : InternedConstructorTemplates.State Symbol Guard) (values : List (Value Symbol Guard))
    (available : Values heap values) : Values heap (EqualityLeafProjectionRuntimeEmpty.propagate values) := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · exact (SourceEqualityEmptyPropagation.erased_scope heap values).1
  · exact available

/-- Each propagated child preserves every signed path domain of its original child. -/
theorem propagate_transport (values : List (Value Symbol Guard)) :
    All₂ Transport values (EqualityLeafProjectionRuntimeEmpty.propagate values) := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · rename_i condition
    clear condition
    induction values with
    | nil => exact .nil
    | cons value values ih =>
        refine .cons ?_ ih
        intro path _
        cases path <;> simp only [NodeClosed, Value.free]
  · rename_i condition
    clear condition
    induction values with
    | nil => exact .nil
    | cons value values ih => exact .cons (fun _ domain => domain) ih

/-- Final propagation retains an arbitrary tracked forest path domain. -/
theorem propagate_domains (values : List (Value Symbol Guard)) (path : List Int)
    (domain : ForestClosed path values) : ForestClosed path (EqualityLeafProjectionRuntimeEmpty.propagate values) :=
  transport_forest (propagate_transport values) path domain

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- A completed right fold derives every head capture domain from the actual tail output. -/
theorem fold_domains {records values results} {before after : NativeState width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      ∀ path : List Int, ForestClosed path values → ForestClosed path results := by
  induction trace with
  | nil => exact ⟨ready, pure_keeps _ ready.semantic.ready, available, fun _ domain => domain⟩
  | cons tail head ih =>
      have first := ih (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => active record (List.mem_cons_of_mem _ member)) ready available
        (fun record member => domains record (List.mem_cons_of_mem _ member))
      have last := SourceCurrentClassEditDomains.class_domains head (coherent _ List.mem_cons_self) (active _ List.mem_cons_self)
        first.1 first.2.2.1 (fun path member => first.2.2.2 _ (domains _ List.mem_cons_self path member))
      exact ⟨last.1, first.2.1.trans last.2.1, last.2.2.1, fun path domain => last.2.2.2 path (first.2.2.2 path domain)⟩

/-- A complete source pass retains every original tracked path through its final literal propagation. -/
theorem pass_domains {records values results} {before after : NativeState width Symbol Guard}
    (trace : Pass emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      ∀ path : List Int, ForestClosed path values → ForestClosed path results := by
  cases trace with
  | done fold =>
      have checked := fold_domains emptyGuard conjoin clear top fold coherent active ready available domains
      exact ⟨checked.1, checked.2.1, propagate_available _ _ checked.2.2.1,
        fun path domain => propagate_domains _ path (checked.2.2.2 path domain)⟩

/-- A completed checked class-fold worker derives its actual returned path domains and physical state. -/
theorem fold_verified (e p h c n : Nat) (records : List SourceEqualityClassOrder.Record)
    (values results : List (Value Symbol Guard)) (before after : NativeState width Symbol Guard)
    (ranges : Ranges emptyGuard conjoin clear top records values before)
    (done : SourceEqualityClassFoldWorker.fold emptyGuard conjoin clear top e p h c n records values before = .done results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      ∀ path : List Int, ForestClosed path values → ForestClosed path results :=
  fold_domains emptyGuard conjoin clear top
    (SourceEqualityClassFoldWorkerProofs.fold_graph emptyGuard conjoin clear top e p h c n records values before ranges results after done)
    coherent active ready available domains

/-- A completed checked pass derives its final domains without a whole-forest closedness premise. -/
theorem pass_verified (e p h c n : Nat) (records : List SourceEqualityClassOrder.Record)
    (values results : List (Value Symbol Guard)) (before after : NativeState width Symbol Guard)
    (ranges : Ranges emptyGuard conjoin clear top records values before)
    (done : SourceEqualityClassFoldWorker.pass emptyGuard conjoin clear top e p h c n records values before = .done results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧
      ∀ path : List Int, ForestClosed path values → ForestClosed path results :=
  pass_domains emptyGuard conjoin clear top
    (SourceEqualityClassFoldWorkerProofs.pass_graph emptyGuard conjoin clear top e p h c n records values before ranges results after done)
    coherent active ready available domains

end MicroCFTA.SourceCurrentClassFoldDomains
