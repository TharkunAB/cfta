import MicroCFTA.SourceEmptinessClassFold

/-!
# Captured class tasks and shared completed results

A row stores original child values and handles for delayed class folds.
Capture stores the original forest without running a projection or native
intersection. A first force runs the actual fold at its reached native state.
Later forces return the stored complete result without native effects.
The force graph uses the closed resident input domain. It does not establish
general native completion or a GHC heap representation.
-/
namespace MicroCFTA.SourceEmptinessTasks
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped
open SourceEmptinessClassFold

/-- A pending requirement is an original value or a captured class handle. -/
inductive Task (Symbol Guard : Type) where
  | value (value : Value Symbol Guard)
  | captured (handle : Nat)

/-- A class task retains its original forest and stored path order. -/
structure Body (Symbol Guard : Type) where
  children : List (Value Symbol Guard)
  paths : List (List Int)

/-- A captured task stores its complete result after the first force. -/
structure Cell (Symbol Guard : Type) where
  body : Body Symbol Guard
  result : Option (Value Symbol Guard)

/-- Task storage accompanies the actual native constructor, domain, and memo state. -/
structure State (width : Nat) (Symbol Guard : Type) where
  native : SourceRecursiveIntersectionThunks.State width Symbol Guard
  next : Nat
  cells : Nat → Option (Cell Symbol Guard)

/-- Read a completed requirement without forcing a suspended class. -/
def read (state : State width Symbol Guard) : Task Symbol Guard → Option (Value Symbol Guard)
  | .value value => some value
  | .captured handle => (state.cells handle).bind Cell.result

/-- Each captured forest and completed result remains in the current closed resident domain. -/
def CellsReady (state : State width Symbol Guard) : Prop :=
  ∀ handle cell, state.cells handle = some cell →
    Values state.native.machine.heap cell.body.children ∧ ClosedValues cell.body.children ∧
      ∀ value, cell.result = some value → Available state.native.machine.heap value ∧ value.free = []

/-- Between tasks the native tables are idle and unused task handles are absent. -/
structure Ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) : Prop where
  native : IdleReady emptyGuard conjoin state.native
  fresh : ∀ handle, state.next ≤ handle → state.cells handle = none
  cells : CellsReady state

/-- Every previously completed task keeps its same complete result. -/
def Retains (before after : State width Symbol Guard) : Prop :=
  ∀ task value, read before task = some value → read after task = some value

/-- An unchanged task store retains every complete result. -/
theorem Retains.refl (state : State width Symbol Guard) : Retains state state := fun _ _ found => found

/-- Complete task results remain stable through consecutive task effects. -/
theorem Retains.trans {before middle after : State width Symbol Guard}
    (first : Retains before middle) (second : Retains middle after) : Retains before after :=
  fun task value found => second task value (first task value found)

/-- Advance only the native state after an actual source constructor operation. -/
def advanceNative (before : State width Symbol Guard)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) : State width Symbol Guard :=
  { before with native := native }

/-- A native-state advance leaves all stored task results unchanged. -/
theorem advanceNative_retains (before : State width Symbol Guard)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retains before (advanceNative before native) := fun _ _ found => found

/-- Actual native heap preservation transports all captured forests and completed results. -/
theorem Ready.advanceNative [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {before : State width Symbol Guard}
    (ready : Ready emptyGuard conjoin before) (native : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (nativeReady : IdleReady emptyGuard conjoin native)
    (keeps : Keeps before.native.machine.heap native.machine.heap) :
    Ready emptyGuard conjoin (advanceNative before native) := by
  refine ⟨nativeReady, ready.fresh, ?_⟩
  intro handle cell found
  have original := ready.cells handle cell found
  refine ⟨fun child member => keeps.available child (original.1 child member), original.2.1, ?_⟩
  intro result completed
  have valid := original.2.2 result completed
  exact ⟨keeps.available result valid.1, valid.2⟩

/-- Start a task scope with the actual native state and no captured classes. -/
def start (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) : State width Symbol Guard :=
  ⟨native, 0, fun _ => none⟩

/-- An idle native input derives the empty task store invariant. -/
theorem start_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : IdleReady emptyGuard conjoin native) :
    Ready emptyGuard conjoin (start native) :=
  ⟨ready, fun _ _ => rfl, fun _ _ impossible => by cases impossible⟩

/-- Capture a class without running its projection or intersection work. -/
def capture (body : Body Symbol Guard) (state : State width Symbol Guard) :
    Task Symbol Guard × State width Symbol Guard :=
  (.captured state.next,
    { state with
      next := state.next + 1
      cells := fun handle => if handle = state.next then some ⟨body, none⟩ else state.cells handle })

/-- A captured class has no native effect. -/
theorem capture_native (body : Body Symbol Guard) (state : State width Symbol Guard) :
    (capture body state).2.native = state.native := rfl

/-- A new captured class remains suspended until its first force. -/
theorem capture_suspended (body : Body Symbol Guard) (state : State width Symbol Guard) :
    read (capture body state).2 (capture body state).1 = none := by
  simp [capture, read]

/-- Fresh capture preserves all prior completed task results. -/
theorem capture_retains [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} (body : Body Symbol Guard)
    (state : State width Symbol Guard) (ready : Ready emptyGuard conjoin state) :
    Retains state (capture body state).2 := by
  intro task value found
  cases task with
  | value original => exact found
  | captured handle =>
      by_cases same : handle = state.next
      · subst handle
        simp only [read, ready.fresh state.next (Nat.le_refl _), Option.bind_none] at found
        cases found
      · simpa only [read, capture, same, ↓reduceIte] using found

/-- Capture derives readiness from the closed available original forest. -/
theorem capture_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} (body : Body Symbol Guard)
    (state : State width Symbol Guard) (ready : Ready emptyGuard conjoin state)
    (available : Values state.native.machine.heap body.children) (closed : ClosedValues body.children) :
    Ready emptyGuard conjoin (capture body state).2 := by
  refine ⟨ready.native, ?_, ?_⟩
  · intro handle beyond
    have different : handle ≠ state.next := by dsimp only [capture] at beyond; omega
    have absent := ready.fresh handle (by dsimp only [capture] at beyond; omega)
    simpa only [capture, different, ↓reduceIte] using absent
  · intro handle cell found
    by_cases same : handle = state.next
    · have actual : cell = ⟨body, none⟩ := by simpa only [capture, same, ↓reduceIte, Option.some.injEq] using found.symm
      subst cell
      exact ⟨available, closed, fun _ impossible => by cases impossible⟩
    · exact ready.cells handle cell (by simpa only [capture, same, ↓reduceIte] using found)

/-- Store one actual fold result and its returned native state at the original handle. -/
def finish (before : State width Symbol Guard) (handle : Nat) (cell : Cell Symbol Guard)
    (value : Value Symbol Guard) (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    State width Symbol Guard :=
  { before with
    native := native
    cells := fun current => if current = handle then some {cell with result := some value} else before.cells current }

/-- A completed force reads its original value, shared result, or actual first native fold. -/
inductive Force [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    Task Symbol Guard → State width Symbol Guard → Value Symbol Guard → State width Symbol Guard → Prop where
  | value (available : Available before.native.machine.heap value) (closed : value.free = []) :
      Force emptyGuard conjoin (.value value) before value before
  | hit (found : before.cells handle = some cell) (completed : cell.result = some value) :
      Force emptyGuard conjoin (.captured handle) before value before
  | miss (found : before.cells handle = some cell) (suspended : cell.result = none)
      (fold : Fold emptyGuard conjoin cell.body.children cell.body.paths before.native value native) :
      Force emptyGuard conjoin (.captured handle) before value (finish before handle cell value native)

/-- Completing a suspended class retains every previously completed task result. -/
theorem finish_retains (before : State width Symbol Guard) (handle : Nat) (cell : Cell Symbol Guard)
    (value : Value Symbol Guard) (native : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (found : before.cells handle = some cell) (suspended : cell.result = none) :
    Retains before (finish before handle cell value native) := by
  intro task original completed
  cases task with
  | value => exact completed
  | captured current =>
      by_cases same : current = handle
      · subst current
        simp only [read, found, Option.bind_some, suspended] at completed
        cases completed
      · simpa only [read, finish, same, ↓reduceIte] using completed

/-- A first native fold preserves captured forests and proves its new completed result valid. -/
theorem finish_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} (before : State width Symbol Guard)
    (ready : Ready emptyGuard conjoin before) (handle : Nat) (cell : Cell Symbol Guard)
    (found : before.cells handle = some cell) (value : Value Symbol Guard)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (nativeReady : IdleReady emptyGuard conjoin native)
    (keeps : Keeps before.native.machine.heap native.machine.heap)
    (available : Available native.machine.heap value) (closed : value.free = []) :
    Ready emptyGuard conjoin (finish before handle cell value native) := by
  have issued : handle < before.next := by
    by_cases earlier : handle < before.next
    · exact earlier
    · have absent := ready.fresh handle (by omega)
      rw [found] at absent
      cases absent
  refine ⟨nativeReady, ?_, ?_⟩
  · intro current beyond
    have different : current ≠ handle := by dsimp only [finish] at beyond; omega
    simpa only [finish, different, ↓reduceIte] using ready.fresh current beyond
  · intro current stored present
    by_cases same : current = handle
    · have actual : stored = {cell with result := some value} := by
        simpa only [finish, same, ↓reduceIte, Option.some.injEq] using present.symm
      subst stored
      have original := ready.cells handle cell found
      refine ⟨fun child member => keeps.available child (original.1 child member), original.2.1, ?_⟩
      intro result completed
      have equal : value = result := Option.some.inj completed
      subst result
      exact ⟨available, closed⟩
    · have original := ready.cells current stored (by simpa only [finish, same, ↓reduceIte] using present)
      refine ⟨fun child member => keeps.available child (original.1 child member), original.2.1, ?_⟩
      intro result completed
      have old := original.2.2 result completed
      exact ⟨keeps.available result old.1, old.2⟩

/-- Each actual force derives physical readiness, closed output, and stable shared results. -/
theorem Force.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {task : Task Symbol Guard} {before after : State width Symbol Guard} {value : Value Symbol Guard}
    (trace : Force emptyGuard conjoin task before value after) (ready : Ready emptyGuard conjoin before) :
    Ready emptyGuard conjoin after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ value.free = [] ∧
      Retains before after ∧ read after task = some value := by
  cases trace with
  | value available closed =>
      exact ⟨ready, pure_keeps _ ready.native.semantic.ready, available, closed, .refl _, rfl⟩
  | hit found completed =>
      have valid := (ready.cells _ _ found).2.2 _ completed
      exact ⟨ready, pure_keeps _ ready.native.semantic.ready, valid.1, valid.2, .refl _, by simp [read, found, completed]⟩
  | miss found suspended fold =>
      have original := ready.cells _ _ found
      have actual := fold.effects ready.native original.1 original.2.1
      exact ⟨finish_ready _ ready _ _ found _ _ actual.1 actual.2.1 actual.2.2.1 actual.2.2.2,
        actual.2.1, actual.2.2.1, actual.2.2.2, finish_retains _ _ _ _ _ found suspended,
        by simp [read, finish]⟩

end MicroCFTA.SourceEmptinessTasks
