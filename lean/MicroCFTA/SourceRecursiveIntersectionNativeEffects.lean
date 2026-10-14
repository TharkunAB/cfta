import MicroCFTA.SourceRecursiveIntersectionNativeTrace

/-!
# Physical effects inside native memo execution

Constructor work, actual domain entry, and optional-binder construction
retain both pending memo families. Pending construction keeps its exact new
heap and original continuation. Completion frames still require concrete
source provenance, which whole native execution must derive.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Native constructor work retains the exact physical source worker and its returned cache. -/
theorem work_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (job : Work Symbol Guard X) (next : X → Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    let actual := InternedConstructorTemplates.run job state.machine.heap
    step emptyGuard conjoin (.work job next) state = .yielded (next actual.1) (advance state { state.machine with heap := actual.2 }) := rfl

/-- Actual constructor verification retains both memo families through native work. -/
theorem work_step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (job : Work Symbol Guard X)
    (property : InternedConstructorTemplates.State Symbol Guard → X → Prop)
    (verified : InternedNestedFacts.Verified state.machine.heap (InternedNestedConstruction.work job state.machine.heap) property)
    (next : X → Code Symbol Guard A) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin (step emptyGuard conjoin (.work job next) state).state := by
  have checked := work_checked state.machine valid.machine job property verified
  exact advance_valid width emptyGuard conjoin state valid _ checked.valid checked.extension

/-- Native domain entry uses the original canonical allocation before entering the continuation. -/
theorem enter_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (first second : Nat)
    (next : Interned DomainKey → Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    let actual := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second
    step emptyGuard conjoin (.enter domain left right first second next) state =
      .yielded (next actual.1) (advance state { state.machine with domains := actual.2 }) := rfl

/-- Actual canonical domain allocation retains every pending memo request and creates a valid body domain. -/
theorem enter_step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (domain : Interned DomainKey) (known : Domain state.machine domain) (left right : Value Symbol Guard)
    (leftAvailable : InternedProbeProvenance.Available state.machine.heap left)
    (rightAvailable : InternedProbeProvenance.Available state.machine.heap right) (first second : Nat)
    (next : Interned DomainKey → Code Symbol Guard A) :
    let actual := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin (step emptyGuard conjoin (.enter domain left right first second next) state).state ∧
      Domain (step emptyGuard conjoin (.enter domain left right first second next) state).state.machine actual.1 := by
  have checked := entered state.machine valid.machine domain known left right leftAvailable rightAvailable first second
  exact ⟨advance_valid width emptyGuard conjoin state valid _ checked.1 checked.2.1, checked.2.2⟩

/-- Original physical binding reads retain every current source and memo cache. -/
theorem read_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (name : Nat) (next : Option (Value Symbol Guard) → Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    step emptyGuard conjoin (.read name next) state = .yielded (next (SourcePreparedSharedRows.read state.machine.heap name)) state := rfl

/-- Completed optional-binder construction enters its continuation at the exact returned source heap. -/
theorem optionalBinder_done_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (key : Nat × Nat) (body value : Value Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (after : InternedConstructorTemplates.State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap = .done value after) :
    step emptyGuard conjoin (.optionalBinder key body next) state = .yielded (next value) (advance state { state.machine with heap := after }) := by
  simp only [step, done]

/-- Pending optional-binder construction retains its actual installed key, new heap, and original continuation. -/
theorem optionalBinder_pending_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (key : Nat × Nat) (body : Value Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (pending : NodeKey) (after : InternedConstructorTemplates.State Symbol Guard)
    (blocked : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap = .pending pending after) :
    step emptyGuard conjoin (.optionalBinder key body next) state =
      .blocked (.constructor pending) (.optionalBinder key body next) (advance state { state.machine with heap := after }) := by
  simp only [step, blocked]

/-- Actual optional-binder verification retains both memo families on completion and pending outcomes. -/
theorem optionalBinder_step_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (key : Nat × Nat) (body : Value Symbol Guard)
    (available : InternedProbeProvenance.Available state.machine.heap body) (next : Value Symbol Guard → Code Symbol Guard A) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin (step emptyGuard conjoin (.optionalBinder key body next) state).state := by
  have verified := SourceRecursiveIntersectionMaybeMu.verified key body state.machine.heap valid.machine.1 available
  have checked := construction_checked state.machine valid.machine _ InternedProbeProvenance.Available verified
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap with
  | done value after =>
    have finalValid := checked.valid
    have growth := checked.extension
    simp only [actual, construction, Result.state] at finalValid growth
    simp only [step, actual, Outcome.state]
    exact advance_valid width emptyGuard conjoin state valid _ finalValid growth
  | pending pending after =>
    have finalValid := checked.valid
    have growth := checked.extension
    simp only [actual, construction, Result.state] at finalValid growth
    simp only [step, actual, Outcome.state]
    exact advance_valid width emptyGuard conjoin state valid _ finalValid growth

end MicroCFTA.SourceRecursiveIntersectionNative
