import MicroCFTA.SourceMergedAPI
import MicroCFTA.SourceEqualityNativeScoped

/-!
# General merging in an existing native equality state

Each demanded merge uses the actual constructor cache. Its wrapper retains
the domain and both native memo tables. Original captured values remain
available through the returned constructor histories.
-/
namespace MicroCFTA.SourceEqualityNativeMerge
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityNativeScoped
open InternedGuardedLanguage (meaning)

/-- One actual general merge request advances only its constructor heap. -/
inductive Merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (clear : Guard → Bool) (top : Guard) (value : Value Symbol Guard) :
    SourceRecursiveIntersectionThunks.State width Symbol Guard → Value Symbol Guard →
      SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | done (fuel : Nat) (actual : SourceMergedWorker.execute clear top fuel value before.machine.heap = .done result heap) :
      Merge clear top value before result (advanceHeap before heap)

/-- Successful demanded merging retains all native tables and every next-request premise. -/
theorem Merge.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard} {value result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Merge clear top value before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Available before.machine.heap value) (closed : value.free = []) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | done fuel actual =>
      have checked := SourceMergedSoundness.execute_covers clear top (fun _ _ => true) (fun _ _ => False)
        (fun _ _ _ => rfl) (fun _ => rfl) fuel value before.machine.heap ready.semantic available closed result _ actual
      exact ⟨ready.advance _ checked.1.1 checked.1.2, checked.1.1, checked.2.1, checked.2.2.1, rfl, rfl, rfl⟩

/-- Demanded general merging preserves the independent language at its actual source cache. -/
theorem Merge.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard} {value result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Merge clear top value before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Available before.machine.heap value) (closed : value.free = [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true) :
    ∀ term, meaning holds ambient value term → meaning holds ambient result term := by
  cases trace with
  | done fuel actual =>
      exact (SourceMergedSoundness.execute_covers clear top holds ambient clearTrue topTrue fuel value before.machine.heap
        ready.semantic available closed result _ actual).2.2.2

/-- Every closed available demanded merge completes finitely inside its existing full native state. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (value : Value Symbol Guard) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (available : Available before.machine.heap value) (closed : value.free = []) :
    ∃ result after, Merge clear top value before result after ∧ IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  obtain ⟨bound, result, heap, done, _⟩ := SourceMergedCompletion.execute_complete clear top value before.machine.heap ready.semantic available closed
  have trace : Merge clear top value before result (advanceHeap before heap) := .done bound (done bound (Nat.le_refl _))
  exact ⟨result, _, trace, trace.effects ready available closed⟩

end MicroCFTA.SourceEqualityNativeMerge
