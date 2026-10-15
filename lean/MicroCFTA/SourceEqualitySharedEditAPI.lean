import MicroCFTA.SourceEqualitySharedEditRetention
import MicroCFTA.SourceEqualitySharedEditComplete
import MicroCFTA.SourceEqualitySharedEditWorkerComplete
import MicroCFTA.SourceEqualityEditCompiledPaths

/-!
# Public execution contracts for shared target edits

Actual source graphs agree with successful bounded execution. Stable
execution derives uniqueness of values, complete native state, and shared
closure slots. Local range checks derive finite execution.
-/
namespace MicroCFTA.SourceEqualitySharedEditAPI
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualitySharedTargetState SourceEqualitySharedTargetWorker SourceEqualitySharedEditGraph
open SourceEqualityEdits SourceEqualitySharedEditRanges SourceEqualitySharedEditEffects
open SourceEqualitySharedEditWorker SourceEqualitySharedEditWorkerSound SourceEqualitySharedEditWorkerComplete
open InternedGuardedLanguage (meaning)

variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))

/-- Checked successful child-list execution gives the literal native list graph. -/
theorem list_graph (fuel p readFuel c nativeFuel : Nat) (edits : Edits EqualityNormalize.Path) (values : List (Value Symbol Guard))
    (before : SharedState width Symbol Guard) (ranges : ListRanges emptyGuard conjoin clear top record originals edits values before)
    (results : List (Value Symbol Guard)) (after : SharedState width Symbol Guard)
    (done : editList (edit emptyGuard conjoin clear top record originals fuel p readFuel c nativeFuel) edits values before = .done results after) :
    EditList emptyGuard conjoin clear top record originals edits values before results after := by
  cases edits with
  | editAt target =>
      have parts := Result.done.inj done
      cases parts.1; cases parts.2; exact .leaf
  | editBelow entries =>
      exact .children (children_graph emptyGuard conjoin clear top record originals (edit emptyGuard conjoin clear top record originals fuel p readFuel c nativeFuel)
        (edit_graph emptyGuard conjoin clear top record originals fuel p readFuel c nativeFuel) entries 0 values before ranges results after done)

/-- Every checked source node graph has exactly a successful bounded native execution. -/
theorem node_execution_iff (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard) (before : SharedState width Symbol Guard)
    (ranges : NodeRanges emptyGuard conjoin clear top record originals edits value before) (result : Value Symbol Guard) (after : SharedState width Symbol Guard) :
    EditNode emptyGuard conjoin clear top record originals edits value before result after ↔
      ∃ fuel p readFuel c nativeFuel, edit emptyGuard conjoin clear top record originals fuel p readFuel c nativeFuel edits value before = .done result after := by
  constructor
  · intro trace
    obtain ⟨fuel, p, readFuel, c, nativeFuel, stable⟩ := node_stable emptyGuard conjoin clear top record originals trace
    exact ⟨fuel, p, readFuel, c, nativeFuel, stable fuel p readFuel c nativeFuel (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, p, readFuel, c, nativeFuel, done⟩
    exact edit_graph emptyGuard conjoin clear top record originals fuel p readFuel c nativeFuel edits value before ranges result after done

/-- Every checked source list graph has exactly a successful bounded native execution. -/
theorem list_execution_iff (edits : Edits EqualityNormalize.Path) (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard)
    (ranges : ListRanges emptyGuard conjoin clear top record originals edits values before) (results : List (Value Symbol Guard)) (after : SharedState width Symbol Guard) :
    EditList emptyGuard conjoin clear top record originals edits values before results after ↔
      ∃ fuel p readFuel c nativeFuel, editList (edit emptyGuard conjoin clear top record originals fuel p readFuel c nativeFuel) edits values before = .done results after := by
  constructor
  · intro trace
    obtain ⟨fuel, p, readFuel, c, nativeFuel, stable⟩ := list_stable emptyGuard conjoin clear top record originals trace
    exact ⟨fuel, p, readFuel, c, nativeFuel, stable fuel p readFuel c nativeFuel (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, p, readFuel, c, nativeFuel, done⟩
    exact list_graph emptyGuard conjoin clear top record originals fuel p readFuel c nativeFuel edits values before ranges results after done

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Stable executions determine one result and one complete native state. -/
theorem stable_unique {evaluation : Nat → Nat → Nat → Nat → Nat → Result width Symbol Guard A} {first second : A}
    {afterFirst afterSecond : SharedState width Symbol Guard} (left : StableRun evaluation first afterFirst)
    (right : StableRun evaluation second afterSecond) : first = second ∧ afterFirst = afterSecond := by
  obtain ⟨firstBound, firstProjection, firstRead, firstComparison, firstNative, firstStable⟩ := left
  obtain ⟨secondBound, secondProjection, secondRead, secondComparison, secondNative, secondStable⟩ := right
  exact Result.done.inj ((firstStable (max firstBound secondBound) (max firstProjection secondProjection) (max firstRead secondRead) (max firstComparison secondComparison) (max firstNative secondNative)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)).symm.trans
      (secondStable (max firstBound secondBound) (max firstProjection secondProjection) (max firstRead secondRead) (max firstComparison secondComparison) (max firstNative secondNative)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

/-- Actual node graphs retain one result and full returned native state. -/
theorem node_unique {edits value before first second afterFirst afterSecond}
    (left : EditNode (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record originals edits value before first afterFirst)
    (right : EditNode emptyGuard conjoin clear top record originals edits value before second afterSecond) : first = second ∧ afterFirst = afterSecond :=
  stable_unique (node_stable emptyGuard conjoin clear top record originals left) (node_stable emptyGuard conjoin clear top record originals right)

/-- Actual compiled list graphs retain one result forest and full returned native state. -/
theorem list_unique {edits values before first second afterFirst afterSecond}
    (left : EditList (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record originals edits values before first afterFirst)
    (right : EditList emptyGuard conjoin clear top record originals edits values before second afterSecond) : first = second ∧ afterFirst = afterSecond :=
  stable_unique (list_stable emptyGuard conjoin clear top record originals left) (list_stable emptyGuard conjoin clear top record originals right)


/-- Local range checks derive a finite stable shared node execution and every output invariant. -/
theorem node_complete (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals) (closed : ClosedValues originals)
    {edits value before} (ranges : NodeRanges (width := width) emptyGuard conjoin clear top record originals edits value before)
    (allowed : Allowed record edits) (ready : Ready emptyGuard conjoin clear top record originals base before)
    (available : Available before.native.machine.heap value) (inputClosed : value.free = []) :
    ∃ result after, EditNode emptyGuard conjoin clear top record originals edits value before result after ∧
      Ready emptyGuard conjoin clear top record originals base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧ SourceEqualitySharedTargetForce.Retains before after ∧
      StableRun (fun e p h c n => edit emptyGuard conjoin clear top record originals e p h c n edits value before) result after := by
  obtain ⟨result, after, trace, finalReady, keeps, resident, resultClosed⟩ :=
    SourceEqualitySharedEditComplete.node emptyGuard conjoin clear top record originals base known closed ranges allowed ready available inputClosed
  exact ⟨result, after, trace, finalReady, keeps, resident, resultClosed,
    SourceEqualitySharedEditRetention.node emptyGuard conjoin clear top record originals trace, node_stable emptyGuard conjoin clear top record originals trace⟩

/-- Local range checks derive a finite stable source child-list execution with actual shared targets. -/
theorem list_complete (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals) (closed : ClosedValues originals)
    {edits values before} (ranges : ListRanges (width := width) emptyGuard conjoin clear top record originals edits values before)
    (allowed : Allowed record edits) (ready : Ready emptyGuard conjoin clear top record originals base before)
    (available : Values before.native.machine.heap values) (inputClosed : ClosedValues values) :
    ∃ results after, EditList emptyGuard conjoin clear top record originals edits values before results after ∧
      Ready emptyGuard conjoin clear top record originals base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Values after.native.machine.heap results ∧ ClosedValues results ∧ SourceEqualitySharedTargetForce.Retains before after ∧
      StableRun (fun e p h c n => editList (edit emptyGuard conjoin clear top record originals e p h c n) edits values before) results after := by
  obtain ⟨results, after, trace, finalReady, keeps, resident, resultClosed⟩ :=
    SourceEqualitySharedEditComplete.list emptyGuard conjoin clear top record originals base known closed ranges allowed ready available inputClosed
  refine ⟨results, after, trace, finalReady, keeps, resident, resultClosed, ?_, list_stable emptyGuard conjoin clear top record originals trace⟩
  cases trace with
  | leaf => exact fun _ _ present => present
  | children trace => exact SourceEqualitySharedEditRetention.children emptyGuard conjoin clear top record originals trace

end MicroCFTA.SourceEqualitySharedEditAPI
