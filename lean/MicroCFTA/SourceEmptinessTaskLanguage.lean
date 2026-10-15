import MicroCFTA.SourceEmptinessTaskTrace

/-!
# Common accepted subtrees through shared class results

Each filled task cell retains the common selected proper subtrees of its
captured original forest. Actual first folds establish this property. Hits
reuse it. Pure captures and complete row reads preserve saved results.
This is a one-sided language property of reached complete-record traces.
It does not establish whole exploration completion or exact lazy demand.
-/
namespace MicroCFTA.SourceEmptinessTaskLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEmptinessTasks SourceEmptinessClassFold
open InternedGuardedLanguage (meaning)

/-- A completed class result includes every common selected proper subtree of its original forest. -/
def Includes (holds : Guard → Term Symbol → Bool) (body : Body Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∀ (ambient : InternedGuardedLanguage.Env Symbol) symbol terms part,
    (∀ path ∈ body.paths, path ≠ []) → All₂ (meaning holds ambient) body.children terms →
    (∀ path ∈ body.paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) →
    meaning holds ambient value part

/-- Every filled cell has the common-subtree property for its own exact captured body. -/
def Saved (holds : Guard → Term Symbol → Bool) (state : State width Symbol Guard) : Prop :=
  ∀ handle cell value, state.cells handle = some cell → cell.result = some value → Includes holds cell.body value

/-- An empty task scope has no saved semantic obligation. -/
theorem start_saved (holds : Guard → Term Symbol → Bool)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Saved holds (start native) := by
  intro handle cell value impossible
  cases impossible

/-- A native-only advance retains each original cell and its saved semantic property. -/
theorem advance_saved (holds : Guard → Term Symbol → Bool) (before : State width Symbol Guard)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) (saved : Saved holds before) :
    Saved holds (advanceNative before native) := saved

/-- Pure capture adds a suspended cell and retains all earlier saved semantic properties. -/
theorem capture_saved (holds : Guard → Term Symbol → Bool) (body : Body Symbol Guard)
    (before : State width Symbol Guard) (saved : Saved holds before) : Saved holds (capture body before).2 := by
  intro handle cell value found completed
  by_cases same : handle = before.next
  · have actual : cell = ⟨body, none⟩ := by
      simpa only [capture, same, ↓reduceIte, Option.some.injEq] using found.symm
    subst cell
    cases completed
  · exact saved handle cell value (by simpa only [capture, same, ↓reduceIte] using found) completed

/-- Saving an actual included result preserves the semantic property of all cells. -/
theorem finish_saved (holds : Guard → Term Symbol → Bool) (before : State width Symbol Guard)
    (handle : Nat) (cell : Cell Symbol Guard) (value : Value Symbol Guard)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) (saved : Saved holds before)
    (included : Includes holds cell.body value) : Saved holds (finish before handle cell value native) := by
  intro current stored result found completed
  by_cases same : current = handle
  · have actual : stored = {cell with result := some value} := by
      simpa only [finish, same, ↓reduceIte, Option.some.injEq] using found.symm
    subst stored
    have equal : value = result := Option.some.inj completed
    subst result
    exact included
  · exact saved current stored result (by simpa only [finish, same, ↓reduceIte] using found) completed

/-- Each completed force derives the saved-result invariant from its actual reached fold. -/
theorem force_saved [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    {task : Task Symbol Guard} {before after : State width Symbol Guard} {value : Value Symbol Guard}
    (trace : Force emptyGuard conjoin task before value after) (ready : Ready emptyGuard conjoin before)
    (saved : Saved holds before) : Saved holds after := by
  cases trace with
  | value => exact saved
  | hit => exact saved
  | miss found suspended fold =>
      have original := ready.cells _ _ found
      apply finish_saved holds _ _ _ _ _ saved
      intro ambient symbol terms part nonroot accepted selected
      exact fold.included ready.native original.1 original.2.1 nonroot holds ambient conjoined
        symbol terms part accepted selected

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "TaskState" => SourceEmptinessTasks.State
open SourceEmptinessTaskRows

/-- Capturing ordered classes preserves all saved class semantics without forcing any class. -/
theorem classes_saved (holds : Guard → Term Symbol → Bool) (children : List (Value Symbol Guard))
    (classes : EqualityNormalize.Constraints) (before : TaskState width Symbol Guard) (saved : Saved holds before) :
    Saved holds (captureClasses children classes before).2 := by
  induction classes generalizing before with
  | nil => exact saved
  | cons paths rest ih => exact ih _ (capture_saved holds (classBody children paths) before saved)

/-- The direct child prefix does not change saved semantics when a row captures its classes. -/
theorem row_saved (holds : Guard → Term Symbol → Bool)
    (row : ConservativeEmptinessRows.Row (Value Symbol Guard)) (before : TaskState width Symbol Guard)
    (saved : Saved holds before) : Saved holds (captureRow row before).2 :=
  classes_saved holds row.children row.classes before saved

/-- Complete ordered row capture preserves every prior saved-result semantic property. -/
theorem rows_saved (holds : Guard → Term Symbol → Bool)
    (rows : List (ConservativeEmptinessRows.Row (Value Symbol Guard))) (before : TaskState width Symbol Guard)
    (saved : Saved holds before) : Saved holds (captureRows rows before).2 := by
  induction rows generalizing before with
  | nil => exact saved
  | cons row rest ih => exact ih _ (row_saved holds row before saved)

/-- Actual complete row reads and pure captures preserve the semantic property of all saved results. -/
theorem expose_saved [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) {value : Value Symbol Guard}
    {before after : TaskState width Symbol Guard} {rows : List (List (Task Symbol Guard))}
    (trace : Expose value before rows after) (saved : Saved holds before) : Saved holds after := by
  cases trace with
  | read available closed actual => exact rows_saved holds _ _ saved

/-- A reached worklist derives final saved semantics from its actual force and exposure leaves. -/
theorem run_saved [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (trace : SourceEmptinessTaskTrace.Run (width := width) emptyGuard conjoin budget seen pending before final after) :
    Ready emptyGuard conjoin before → Saved holds before → Saved holds after := by
  induction trace with
  | done => intro ready saved; exact saved
  | empty forced encoded rest ih =>
      intro ready saved
      exact ih (forced.effects ready).1 (force_saved holds conjoined forced ready saved)
  | skipped forced encoded skipped rest ih =>
      intro ready saved
      exact ih (forced.effects ready).1 (force_saved holds conjoined forced ready saved)
  | admit forced encoded fresh exposed rest ih =>
      intro ready saved
      have forcedReady := (forced.effects ready).1
      have first := force_saved holds conjoined forced ready saved
      exact ih (exposed.effects forcedReady).1 (expose_saved holds exposed first)

/-- Original construction starts with no saved cells; each completed reached trace derives all final cell semantics. -/
theorem initial_run_saved [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : SourceEqualityNativeScoped.IdleReady emptyGuard conjoin native)
    (trace : SourceEmptinessTaskTrace.Run (width := width) emptyGuard conjoin budget seen pending (start native) final after) :
    Saved holds after := run_saved holds conjoined trace (start_ready native ready) (start_saved holds native)

end MicroCFTA.SourceEmptinessTaskLanguage
