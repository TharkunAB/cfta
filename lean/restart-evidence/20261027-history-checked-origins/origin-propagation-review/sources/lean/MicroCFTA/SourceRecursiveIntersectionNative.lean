import MicroCFTA.SourceRecursiveIntersectionCompile

/-!
# Resumable recursive node and edge memo execution

Every recursive instruction uses the native typed memo state. A miss
publishes and starts its thunk before the compiled body runs. Yielded and
blocked observations retain their exact continuation and current caches.
Busy demands remain blocked. They do not become successful intersections.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Pending native observations retain the exact requested thunk or constructor key. -/
inductive Blocked where
  | nodeBusy (handle : Nat)
  | edgeBusy (handle : Nat)
  | absentNode (handle : Nat)
  | absentEdge (handle : Nat)
  | constructor (key : NodeKey)
  deriving DecidableEq, Repr

/-- Native observations retain the current control whenever execution can resume. -/
inductive Outcome (width : Nat) (Symbol Guard A : Type) : Type 1 where
  | yielded (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
  | done (value : A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
  | failed (failure : Failure) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
  | blocked (reason : Blocked) (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)

/-- Observe the exact current source and memo caches in every outcome. -/
def Outcome.state : Outcome width Symbol Guard A → SourceRecursiveIntersectionThunks.State width Symbol Guard
  | .yielded _ state | .done _ state | .failed _ state | .blocked _ _ state => state

/-- One native step performs one effect or expands one published recursive request. -/
def step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Outcome width Symbol Guard A :=
  match code with
  | .pure value => .done value state
  | .fail failure => .failed failure state
  | .work job next =>
      let actual := InternedConstructorTemplates.run job state.machine.heap
      .yielded (next actual.1) (advance state { state.machine with heap := actual.2 })
  | .enter domain left right first second next =>
      let entered := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second
      .yielded (next entered.1) (advance state { state.machine with domains := entered.2 })
  | .read name next => .yielded (next (SourcePreparedSharedRows.read state.machine.heap name)) state
  | .optionalBinder key body next =>
      match SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap with
      | .done value after => .yielded (next value) (advance state { state.machine with heap := after })
      | .pending pending after => .blocked (.constructor pending) code (advance state { state.machine with heap := after })
  | .node request next =>
      let selected := lookupNode width request state
      match selected.1 with
      | .direct actual => .yielded ((compileNode actual).bind next) selected.2
      | .memoized handle =>
          let demanded := demandNode handle selected.2
          match demanded.1 with
          | .absent => .blocked (.absentNode handle) code demanded.2
          | .busy => .blocked (.nodeBusy handle) code demanded.2
          | .ready value => .yielded (next value) demanded.2
          | .evaluate actual =>
              .yielded ((compileNode actual).bind fun value => .finishNode handle value (next value)) demanded.2
  | .edge request next =>
      let selected := lookupEdge width request state
      let demanded := demandEdge selected.1 selected.2
      match demanded.1 with
      | .absent => .blocked (.absentEdge selected.1) code demanded.2
      | .busy => .blocked (.edgeBusy selected.1) code demanded.2
      | .ready value => .yielded (next value) demanded.2
      | .evaluate actual =>
          .yielded ((compileEdge emptyGuard conjoin actual).bind fun value => .finishEdge selected.1 value (next value)) demanded.2
  | .finishNode handle value next => .yielded next (SourceRecursiveIntersectionThunks.finishNode handle value state)
  | .finishEdge handle value next => .yielded next (SourceRecursiveIntersectionThunks.finishEdge handle value state)

/-- A finite native bound yields the original remaining code instead of a fabricated result. -/
def execute [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    Nat → Code Symbol Guard A → SourceRecursiveIntersectionThunks.State width Symbol Guard → Outcome width Symbol Guard A
  | 0, code, state => .yielded code state
  | fuel + 1, code, state =>
      match step emptyGuard conjoin code state with
      | .yielded next after => execute emptyGuard conjoin fuel next after
      | .done value after => .done value after
      | .failed failure after => .failed failure after
      | .blocked reason next after => .blocked reason next after

/-- More fuel continues yielded code at its exact returned state. -/
def resume [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (outcome : Outcome width Symbol Guard A) : Outcome width Symbol Guard A :=
  match outcome with
  | .yielded next after => execute emptyGuard conjoin fuel next after
  | .done value after => .done value after
  | .failed failure after => .failed failure after
  | .blocked reason next after => .blocked reason next after

/-- Splitting a finite bound preserves all continuations, memo cells, and physical effects. -/
theorem execute_add [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel extra : Nat) (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    execute emptyGuard conjoin (fuel + extra) code state = resume emptyGuard conjoin extra (execute emptyGuard conjoin fuel code state) := by
  induction fuel generalizing code state with
  | zero => simp only [Nat.zero_add, execute, resume]
  | succ fuel ih =>
    simp only [Nat.succ_add, execute]
    cases next : step emptyGuard conjoin code state with
    | yielded rest after => exact ih rest after
    | done | failed | blocked => rfl

/-- Every yielded native execution can resume without discarding its current effects. -/
theorem yielded_resume [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel extra : Nat) (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (yielded : execute emptyGuard conjoin fuel code state = .yielded next after) :
    execute emptyGuard conjoin (fuel + extra) code state = execute emptyGuard conjoin extra next after := by
  rw [execute_add, yielded]
  rfl

/-- Additional fuel alone cannot change a completed native result or its exact caches. -/
theorem done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel extra : Nat) (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : A) (done : execute emptyGuard conjoin fuel code state = .done value after) :
    execute emptyGuard conjoin (fuel + extra) code state = .done value after := by
  rw [execute_add, done]
  rfl

/-- Additional fuel retains a blocked continuation until its external state changes. -/
theorem blocked_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel extra : Nat) (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (reason : Blocked) (blocked : execute emptyGuard conjoin fuel code state = .blocked reason next after) :
    execute emptyGuard conjoin (fuel + extra) code state = .blocked reason next after := by
  rw [execute_add, blocked]
  rfl

end MicroCFTA.SourceRecursiveIntersectionNative
