import MicroCFTA.SourceRecursiveIntersectionNativeBranchReadback
import MicroCFTA.SourceRecursiveIntersectionMuSchedule

/-!
# Semantic Mu steps from actual native completion

Native evaluation supplies the recursive body, its free-name scope, and
the binder correspondence at every larger replay bound. Only the local
correspondence for the body remains for a full recursive induction.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity pair)
open SourceRecursiveIntersectionScheduleConstructors (Corresponds)
open SourceRecursiveIntersectionScheduleEnvironment (Ordered)

/-- Checked native Mu completion derives a body witness and the exact semantic binder step. -/
theorem native_mu_schedule_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (ready : NodeReady state.machine ⟨domain, left, right⟩)
    (selected : SourceRecursiveIntersectionControl.decision domain.key left right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision domain.key left right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision domain.key left right = .rightMu)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state.machine.heap)
    (guarded : InternedGuardedProbeHeap.Heap state.machine.heap) (ordered : Ordered domain.key.seen)
    (done : execute emptyGuard conjoin fuel (.node ⟨domain, left, right⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨domain, left, right⟩ .pure) state) :
    ∃ bound, ∀ extra, ∃ first second extended bodyValue,
      identity left = some first ∧ identity right = some second ∧
      extended.key = SourceRecursiveIntersectionDomain.extend domain.key
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair first second) ∧
      SourceRecursiveIntersectionKernel.Domain after.machine extended ∧ Available after.machine.heap bodyValue ∧
      SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra) extended (body left) (body right) after.machine =
        .done bodyValue after.machine ∧
      SourceRecursiveIntersectionResultScope.Scope extended.key.seen bodyValue ∧
      ∀ holds shape, Corresponds holds bodyValue shape →
        Corresponds holds value (IntersectSchedule.maybeMu (pair first second) shape) := by
  obtain ⟨afterValid, growth, bound, completed⟩ := native_node_branch_replay emptyGuard conjoin fuel _ state after value valid ready done ranges
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after value done
  have retained := (evaluated.bounds_of_ranges ranges).guarded_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode domain left right state.machine ready) valid
    (semantic_requestNode domain left right state.machine ready) semantic (by intro value; trivial) guarded
  refine ⟨bound, ?_⟩
  intro extra
  have returned := completed extra after.machine (.refl _)
  have muDone : mu (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra)) domain left right after.machine =
      .done value after.machine := by
    rcases selected with selected | selected | selected <;> simpa only [onNode, selected] using returned
  exact mu_schedule_body _ (execute_checked emptyGuard conjoin (bound + extra)) (execute_replay emptyGuard conjoin (bound + extra))
    (SourceRecursiveIntersectionScopeCalls.execute_scoped emptyGuard conjoin (bound + extra))
    domain left right after.machine after.machine afterValid.machine afterValid.machine (ready.1.grows domain growth)
    (growth.available left ready.2.1) (growth.available right ready.2.2) retained.1 retained.2 ordered value after.machine muDone (.refl _)

end MicroCFTA.SourceRecursiveIntersectionNative
