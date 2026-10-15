import MicroCFTA.SourceEqualityNativeEditLanguage
import MicroCFTA.SourceEqualityNativeEditComplete
import MicroCFTA.SourceEqualityNativeEditWorkerComplete
import MicroCFTA.SourceEqualityEditCompiledPaths

/-!
# Public scoped simultaneous native edit contracts

Actual compiled paths retain the original signed compiler. Completion,
execution agreement, and exact languages use captured physical targets in
one real earlier cache. No global LeafLaw is assumed or instantiated.
-/
namespace MicroCFTA.SourceEqualityNativeEditAPI
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityNativeEditGraph
open SourceEqualityEdits SourceEqualityNativeEditRanges SourceEqualityNativeEditEffects
open SourceEqualityNativeEditWorker SourceEqualityNativeEditWorkerSound SourceEqualityNativeEditWorkerComplete
open InternedGuardedLanguage (meaning)

variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)

/-- Checked successful child-list execution gives the literal native list graph. -/
theorem list_graph (fuel readFuel nativeFuel : Nat) (edits : Edits (Value Symbol Guard)) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (ranges : ListRanges emptyGuard conjoin edits values before)
    (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard)
    (done : editList (edit emptyGuard conjoin fuel readFuel nativeFuel) edits values before = .done results after) :
    EditList emptyGuard conjoin edits values before results after := by
  cases edits with
  | editAt target =>
      have parts := Result.done.inj done
      cases parts.1; cases parts.2; exact .leaf
  | editBelow entries =>
      exact .children (children_graph emptyGuard conjoin (edit emptyGuard conjoin fuel readFuel nativeFuel)
        (edit_graph emptyGuard conjoin fuel readFuel nativeFuel) entries 0 values before ranges results after done)

/-- Every checked source node graph has exactly a successful bounded native execution. -/
theorem node_execution_iff (edits : Edits (Value Symbol Guard)) (value : Value Symbol Guard) (before : NativeState width Symbol Guard)
    (ranges : NodeRanges emptyGuard conjoin edits value before) (result : Value Symbol Guard) (after : NativeState width Symbol Guard) :
    EditNode emptyGuard conjoin edits value before result after ↔
      ∃ fuel readFuel nativeFuel, edit emptyGuard conjoin fuel readFuel nativeFuel edits value before = .done result after := by
  constructor
  · intro trace
    obtain ⟨fuel, readFuel, nativeFuel, stable⟩ := node_stable emptyGuard conjoin trace
    exact ⟨fuel, readFuel, nativeFuel, stable fuel readFuel nativeFuel (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, readFuel, nativeFuel, done⟩
    exact edit_graph emptyGuard conjoin fuel readFuel nativeFuel edits value before ranges result after done

/-- Every checked source list graph has exactly a successful bounded native execution. -/
theorem list_execution_iff (edits : Edits (Value Symbol Guard)) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (ranges : ListRanges emptyGuard conjoin edits values before) (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard) :
    EditList emptyGuard conjoin edits values before results after ↔
      ∃ fuel readFuel nativeFuel, editList (edit emptyGuard conjoin fuel readFuel nativeFuel) edits values before = .done results after := by
  constructor
  · intro trace
    obtain ⟨fuel, readFuel, nativeFuel, stable⟩ := list_stable emptyGuard conjoin trace
    exact ⟨fuel, readFuel, nativeFuel, stable fuel readFuel nativeFuel (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨fuel, readFuel, nativeFuel, done⟩
    exact list_graph emptyGuard conjoin fuel readFuel nativeFuel edits values before ranges results after done

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Stable executions determine one result and one complete native state. -/
theorem stable_unique {evaluation : Nat → Nat → Nat → Result width Symbol Guard A} {first second : A}
    {afterFirst afterSecond : NativeState width Symbol Guard} (left : StableRun evaluation first afterFirst)
    (right : StableRun evaluation second afterSecond) : first = second ∧ afterFirst = afterSecond := by
  obtain ⟨firstBound, firstRead, firstNative, firstStable⟩ := left
  obtain ⟨secondBound, secondRead, secondNative, secondStable⟩ := right
  exact Result.done.inj ((firstStable (max firstBound secondBound) (max firstRead secondRead) (max firstNative secondNative)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)).symm.trans
      (secondStable (max firstBound secondBound) (max firstRead secondRead) (max firstNative secondNative)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

/-- Actual node graphs retain one result and full returned native state. -/
theorem node_unique {edits value before first second afterFirst afterSecond}
    (left : EditNode (Symbol := Symbol) (width := width) emptyGuard conjoin edits value before first afterFirst)
    (right : EditNode emptyGuard conjoin edits value before second afterSecond) : first = second ∧ afterFirst = afterSecond :=
  stable_unique (node_stable emptyGuard conjoin left) (node_stable emptyGuard conjoin right)

/-- Actual compiled list graphs retain one result forest and full returned native state. -/
theorem list_unique {edits values before first second afterFirst afterSecond}
    (left : EditList (Symbol := Symbol) (width := width) emptyGuard conjoin edits values before first afterFirst)
    (right : EditList emptyGuard conjoin edits values before second afterSecond) : first = second ∧ afterFirst = afterSecond :=
  stable_unique (list_stable emptyGuard conjoin left) (list_stable emptyGuard conjoin right)

/-- Every completed native list graph has the exact original ordered forest and retained physical-target conditions. -/
theorem list_exact (base : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    {edits values before results after} (trace : EditList (Symbol := Symbol) (width := width) emptyGuard conjoin edits values before results after)
    (valid : SourceEqualityEdits.Valid edits) (captured : Captured base edits) (retained : Keeps base before.machine.heap)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values) :
    ∀ terms, All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms ∧
      SourceEqualityEditAPI.ListCondition (meaning holds ambient) edits terms := by
  cases trace with
  | leaf => intro terms; simp [SourceEqualityEditAPI.ListCondition]
  | children trace =>
      exact SourceEqualityNativeEditLanguage.children_exact emptyGuard conjoin base holds ambient conjoined
        trace valid captured retained ready available closed

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Actual original edit pairs derive captured scope for every retained compiler leaf. -/
theorem compiled_captured (base : InternedConstructorTemplates.State Symbol Guard) (edits : List (Path × Value Symbol Guard))
    (known : ∀ path target, (path, target) ∈ edits → Available base target ∧ target.free = []) : Captured base (build edits) :=
  build_all _ edits known

/-- Actual compiled source edits complete with stable full native state and exact forest language. -/
theorem compiled_complete (base : InternedConstructorTemplates.State Symbol Guard)
    (edits : List (Path × Value Symbol Guard)) (known : ∀ path target, (path, target) ∈ edits → Available base target ∧ target.free = [])
    (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) (retained : Keeps base before.machine.heap)
    (ready : IdleReady emptyGuard conjoin before) (ranges : ListRanges emptyGuard conjoin (build edits) values before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ results after, EditList emptyGuard conjoin (build edits) values before results after ∧ IdleReady emptyGuard conjoin after ∧
      Keeps base after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
      StableRun (fun fuel readFuel nativeFuel => editAll emptyGuard conjoin fuel readFuel nativeFuel edits values before) results after ∧
      ∀ terms, All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms ∧
        SourceEqualityEditAPI.ListCondition (meaning holds ambient) (build edits) terms := by
  have captured := compiled_captured base edits known
  obtain ⟨results, after, trace, finalReady, keeps, resultAvailable, resultClosed⟩ :=
    SourceEqualityNativeEditComplete.list emptyGuard conjoin base ranges captured retained ready available closed
  exact ⟨results, after, trace, finalReady, retained.trans keeps, resultAvailable, resultClosed,
    list_stable emptyGuard conjoin trace, list_exact emptyGuard conjoin base holds ambient conjoined trace (build_valid edits) captured retained ready available closed⟩

/-- Nonoverlapping original paths have exact complete-path physical-target readback for actual native edits. -/
theorem compiled_paths (base : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (edits : List (Path × Value Symbol Guard))
    (disjoint : edits.Pairwise (fun first second => SourceEqualityEditCompiledPaths.Disjoint first.1 second.1))
    (nonroot : ∀ path target, (path, target) ∈ edits → path ≠ [])
    (known : ∀ path target, (path, target) ∈ edits → Available base target ∧ target.free = [])
    {values before results after} (trace : EditList (Symbol := Symbol) (width := width) emptyGuard conjoin (build edits) values before results after)
    (retained : Keeps base before.machine.heap) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) (symbol : Symbol) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms ∧
      ∀ path target, (path, target) ∈ edits → ∀ part,
        SymbolicSignedPaths.lookup (.node symbol terms) path = some part → meaning holds ambient target part := by
  rw [list_exact emptyGuard conjoin base holds ambient conjoined trace (build_valid edits) (compiled_captured base edits known) retained ready available closed terms,
    SourceEqualityEditCompiledPaths.list_condition_exact (meaning holds ambient) edits disjoint nonroot symbol terms]

end MicroCFTA.SourceEqualityNativeEditAPI
