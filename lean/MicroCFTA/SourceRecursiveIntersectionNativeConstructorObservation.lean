import MicroCFTA.SourceRecursiveIntersectionNativeTerminal

/-!
# Successful returns or actual pending constructors

These finite observations exclude source failures, absent handles, and
busy demands. Appended code retains the actual constructor key, remaining
continuation, and complete native state when construction is pending.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- A finite native observation returns a value or reports its actual pending constructor. -/
inductive ReturnsOrPending : Outcome width Symbol Guard A → Prop where
  | done (value : A) (state) : ReturnsOrPending (.done value state)
  | constructor (key : NodeKey) (code : Code Symbol Guard A) (state) : ReturnsOrPending (.blocked (.constructor key) code state)

/-- A return or pending constructor is a finite terminal observation. -/
theorem ReturnsOrPending.terminal {outcome : Outcome width Symbol Guard A} (observed : ReturnsOrPending outcome) : Terminal outcome := by
  cases observed with
  | done value state => exact .done value state
  | constructor key code state => exact .constructor key code state

/-- An actual yielded prefix retains a later return or exact pending constructor. -/
theorem returns_after_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Steps emptyGuard conjoin fuel code state next after)
    (later : ∃ extra, ReturnsOrPending (execute emptyGuard conjoin extra next after)) :
    ∃ total, ReturnsOrPending (execute emptyGuard conjoin total code state) := by
  obtain ⟨extra, observed⟩ := later
  refine ⟨fuel + extra, ?_⟩
  rw [execute_add, trace.execute, resume]
  exact observed

/-- One actual yielded step retains a later return or exact pending constructor. -/
theorem returns_after_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (one : step emptyGuard conjoin code state = .yielded next after)
    (later : ∃ fuel, ReturnsOrPending (execute emptyGuard conjoin fuel next after)) :
    ∃ fuel, ReturnsOrPending (execute emptyGuard conjoin fuel code state) :=
  returns_after_trace emptyGuard conjoin 1 code next state after (.cons _ _ _ _ _ _ 0 one (.refl _ _)) later

/-- Appended code preserves a pending constructor and continues only an actual returned body. -/
theorem returns_bind [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (next : A → Code Symbol Guard B) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (observed : ∃ fuel, ReturnsOrPending (execute emptyGuard conjoin fuel code state))
    (continuation : ∀ fuel value after, execute emptyGuard conjoin fuel code state = .done value after →
      ∃ extra, ReturnsOrPending (execute emptyGuard conjoin extra (next value) after)) :
    ∃ fuel, ReturnsOrPending (execute emptyGuard conjoin fuel (code.bind next) state) := by
  obtain ⟨fuel, observed⟩ := observed
  generalize done : execute emptyGuard conjoin fuel code state = actual at observed
  cases observed with
  | done value after =>
      obtain ⟨steps, _, trace⟩ := done_trace emptyGuard conjoin fuel code state after value done
      exact returns_after_trace emptyGuard conjoin steps (code.bind next) (next value) state after
        (Steps.bind emptyGuard conjoin steps code (.pure value) state after trace next) (continuation fuel value after done)
  | constructor key remaining after =>
      exact ⟨fuel, by rw [execute_bind_constructor emptyGuard conjoin fuel code remaining next state after key done]; exact .constructor _ _ _⟩

end MicroCFTA.SourceRecursiveIntersectionNative
