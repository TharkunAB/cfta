import MicroCFTA.SourceRecursiveIntersectionNative
import MicroCFTA.SourceRecursiveIntersectionMaybeMuDepth
import MicroCFTA.InternedStoredPlanBinderDepthLowerAlgebra

/-!
# Actual native primitive allocation bounds

Pure and completion frames retain every complete Mu record.
Ordinary work preserves its proved no-new-Mu property.
Optional-binder observations include the heap changed by pending construction.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionCode
open InternedStoredPlanBinderDepth InternedStoredPlanBinderDepthProgress

/-- Every finite pure observation retains the original heap. -/
theorem pure_lower [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (value : A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (bound : Nat) :
    Lower state.machine.heap bound (execute emptyGuard conjoin fuel (.pure value) state).state.machine.heap := by
  cases fuel <;> exact lower_refl state.machine.heap bound

/-- Every finite failure observation retains the original heap. -/
theorem fail_lower [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (failure : SourceRecursiveIntersectionKernel.Failure)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (bound : Nat) :
    Lower state.machine.heap bound
      (execute emptyGuard conjoin fuel (.fail failure : Code Symbol Guard A) state).state.machine.heap := by
  cases fuel <;> exact lower_refl state.machine.heap bound

/-- Completing a node memo and returning its value changes no constructor record. -/
theorem finishNode_lower [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel handle : Nat)
    (value : Value Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (bound : Nat) :
    Lower state.machine.heap bound
      (execute emptyGuard conjoin fuel (.finishNode handle value (.pure value)) state).state.machine.heap := by
  cases fuel with
  | zero => exact lower_refl state.machine.heap bound
  | succ fuel => cases fuel <;> exact lower_refl state.machine.heap bound

/-- Completing an edge memo and returning its value changes no constructor record. -/
theorem finishEdge_lower [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel handle : Nat)
    (value : EdgeValue Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (bound : Nat) :
    Lower state.machine.heap bound
      (execute emptyGuard conjoin fuel (.finishEdge handle value (.pure value)) state).state.machine.heap := by
  cases fuel with
  | zero => exact lower_refl state.machine.heap bound
  | succ fuel => cases fuel <;> exact lower_refl state.machine.heap bound

/-- Ordinary work that adds no Mu retains the original record alternatives at every outcome. -/
theorem work_lower [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (job : Work Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (bound : Nat)
    (old : InternedShallowHeap.NoNewMu state.machine.heap (run job state.machine.heap).2) :
    Lower state.machine.heap bound
      (execute emptyGuard conjoin fuel (.work job .pure) state).state.machine.heap := by
  have lower := preserve state.machine.heap _ (lower_refl state.machine.heap bound) old
  cases fuel with
  | zero => exact lower_refl state.machine.heap bound
  | succ fuel => cases fuel <;> exact lower

/-- An actual bounded optional-binder site retains the bound in every native outcome. -/
theorem optionalBinder_lower [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (key : Nat × Nat) (body : Value Symbol Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (bound : Nat)
    (context : InternedFreshOrdinaryContext.Context state.machine.heap [])
    (cached : InternedFreshOrdinaryDepthHeap.Heap state.machine.heap)
    (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (available : Available state.machine.heap body) (small : valueDepth body + 1 ≤ bound) :
    Lower state.machine.heap bound
      (execute emptyGuard conjoin fuel (.optionalBinder key body .pure) state).state.machine.heap := by
  have lower := (SourceRecursiveIntersectionMaybeMu.lower key body state.machine.heap context cached opened available).mono small
  cases fuel with
  | zero => exact lower_refl state.machine.heap bound
  | succ fuel =>
      cases built : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap with
      | pending pending after =>
          simpa only [execute, step, built, Outcome.state, SourceRecursiveIntersectionThunks.advance,
            InternedNestedConstruction.Outcome.state] using lower
      | done value after =>
          cases fuel <;>
            simpa only [execute, step, built, Outcome.state, SourceRecursiveIntersectionThunks.advance,
              InternedNestedConstruction.Outcome.state] using lower

end MicroCFTA.SourceRecursiveIntersectionNative
