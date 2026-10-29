import MicroCFTA.SourcePruningEnumerationParkedRestart
import MicroCFTA.EnumerationIndexSelection

/-!
# Exact candidate consumption at an actual parked restart

The original selected flag is true. The actual parked write disables that
flag and keeps every other flag. The allocation counter stays fixed.
The existing finite candidate count therefore decreases by exactly one.
Every original parked receipt and configured restart result remains.
-/
namespace MicroCFTA.SourcePruningEnumerationParkedRestart
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

private theorem candidates_clear_count
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (uv : Nat)
    (counter : after.core.counter = before.core.counter)
    (inside : uv < before.core.counter) (selected : before.expandable uv = true)
    (flags : ∀ other, after.expandable other =
      if other = uv then false else before.expandable other) :
    (EnumerationIndexSelection.candidates after).length + 1 =
      (EnumerationIndexSelection.candidates before).length := by
  have unique : (EnumerationIndexSelection.candidates before).Nodup :=
    List.nodup_range.filter _
  have present : uv ∈ EnumerationIndexSelection.candidates before := by
    exact List.mem_filter.mpr ⟨List.mem_range.mpr inside, selected⟩
  have removed : EnumerationIndexSelection.candidates after =
      (EnumerationIndexSelection.candidates before).erase uv := by
    rw [unique.erase_eq_filter]
    unfold EnumerationIndexSelection.candidates
    rw [counter, List.filter_filter]
    apply congrArg (fun predicate => (List.range before.core.counter).filter predicate)
    funext other
    rw [flags]
    by_cases same : other = uv <;> simp [same]
  rw [removed, List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

/-- Original selection consumes one candidate on the actual parked branch without a model. -/
theorem selected_complete_with_order_progress
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat) (roots : Nat → Nat)
    (safe : Safe before.core)
    (selection : EnumerationPureSelection.next preference before = .expand uv)
    (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (readFuel handle : Nat) (scs : List Suspended) (value : Value Symbol NativeGuard)
      (readAfter : EnumerationState.State Symbol EnumGuard) (checkFuel : Nat) (repeated : Bool)
      (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      lookupNode heap handle = some value ∧ Available heap value ∧ value.free = [] ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv before.core) =
        [.ok (.unenumerated (some handle) scs, readAfter)]) ∧
      Frame before.core readAfter ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap
        (checkFuel + extra) uv handle scs readAfter) = [.ok (repeated, after.core)]) ∧
      EnumerationDriver.Ready uv after.core ∧ Roots after.core.representatives roots ∧
      PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumerationReferences.IncomingAvoid uv after.core ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (repeated = false → Frame before.core after.core ∧ after.expandable = before.expandable ∧
        after.waiting = before.waiting ∧ after.core.values[uv]? = some (.unenumerated (some handle) scs)) ∧
      (repeated = true → after.core.counter = before.core.counter ∧
        ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          EnumerationOrder.Stratified after.core level frontier) ∧
      (repeated = true → MergedOrdinaryHeight.recursiveBoundary value = true ∧
        after.core.values[uv]? = some (.unenumerated (some handle) []) ∧ after.expandable uv = false ∧
        after.waiting = EnumerationCanonicalWaiting.count roots (-1) scs before.waiting ∧
        ∃ (resolved : EnumerationState.State Symbol EnumGuard) (countFuel : Nat),
          Frame before.core resolved ∧
          Success (representative checkFuel uv) readAfter uv resolved ∧
          recursionKey handle scs ∈ resolved.recursionAncestry uv ∧
          Success (setValue uv (.unenumerated (some handle) [])) resolved () after.core ∧
          ∀ extra, SourcePruningEnumerationNativeIndex.write heap (countFuel + extra) uv
            (.unenumerated (some handle) []) [] scs (EnumerationExpandableIndex.frame resolved before) = some after) ∧
      before.expandable uv = true ∧
      (repeated = true →
        (∀ other, after.expandable other =
          if other = uv then false else before.expandable other) ∧
        (EnumerationIndexSelection.candidates after).length + 1 =
          (EnumerationIndexSelection.candidates before).length) := by
  obtain ⟨inside, selected, _unblocked⟩ :=
    SourcePruningEnumerationSelection.offered before preference uv selection
  obtain ⟨readFuel, handle, scs, value, readAfter, checkFuel, repeated, after, stored, decoded,
    available, closed, readExact, readFrame, checkExact, afterReady, afterPaths, afterRealized,
    afterCounts, afterFlags, incoming, pending, continued, orderPreserved, parked⟩ :=
    selected_complete_with_order heap before preference uv roots safe selection realized paths counts flags
  refine ⟨readFuel, handle, scs, value, readAfter, checkFuel, repeated, after, stored, decoded,
    available, closed, readExact, readFrame, checkExact, afterReady, afterPaths, afterRealized,
    afterCounts, afterFlags, incoming, pending, continued, orderPreserved, parked, selected, ?_⟩
  intro repeatedTrue
  obtain ⟨boundary, _cleared, _disabled, _waiting, resolved, countFuel, _frame, _readRoot,
    _seen, _written, indexed⟩ := parked repeatedTrue
  have actualFlags : ∀ other, after.expandable other =
      if other = uv then false else before.expandable other := by
    have observed := indexed 0
    simp only [Nat.add_zero, SourcePruningEnumerationNativeIndex.write,
      SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some,
      boundary, List.isEmpty_nil, Bool.true_and, Bool.not_true, Option.bind_some,
      EnumerationExpandableIndex.frame] at observed
    cases counted : SourcePruningEnumerationNativeIndex.count countFuel resolved.representatives
        (-1) scs before.waiting with
    | none =>
        simp only [counted, Option.bind_none] at observed
        cases observed
    | some waiting =>
        simp only [counted, Option.bind_some, SourcePruningEnumerationNativeIndex.count,
          Option.some.injEq] at observed
        intro other
        exact (congrArg (fun cache => cache.expandable other) observed).symm
  exact ⟨actualFlags, candidates_clear_count before after uv
    (orderPreserved repeatedTrue).1 inside selected actualFlags⟩

local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {width : Nat}

/-- The exact configured parked restart also consumes one candidate without a model. -/
theorem selected_complete_with_restart_progress
    (caller : SourceCurrentAllocatedPartialState.State width)
    (before : Cached) (preference : List Nat → Option Nat) (uv : Nat)
    (safe : Safe before.core)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (selection : EnumerationPureSelection.next preference before = .expand uv) :
    ∃ (readFuel handle : Nat) (scs : List Suspended)
      (readAfter : EnumerationState.State Symbol Constraint) (checkFuel : Nat) (repeated : Bool) (after : Cached),
      before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv before.core) =
        [.ok (.unenumerated (some handle) scs, readAfter)]) ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        (checkFuel + extra) uv handle scs readAfter) = [.ok (repeated, after.core)]) ∧
      SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after ∧ Safe after.core ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (repeated = true → after.core.counter = before.core.counter ∧
        (∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          EnumerationOrder.Stratified after.core level frontier) ∧
        ∃ countFuel, ∀ extra (stop : Option (Metadata Typing → Nat → Bool))
          (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing),
          ExceptT.run (run caller.checked.native.machine.heap readFuel checkFuel (countFuel + extra) uv
            stop order metadata before before.core) =
            if SourcePruningEnumerationRestart.decision stop order metadata after = some .stuck then []
            else [.ok (some (metadata, SourcePruningEnumerationRestart.decision stop order metadata after), after.core)]) ∧
      before.expandable uv = true ∧
      (repeated = true →
        (∀ other, after.expandable other =
          if other = uv then false else before.expandable other) ∧
        (EnumerationIndexSelection.candidates after).length + 1 =
          (EnumerationIndexSelection.candidates before).length) := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := valid
  obtain ⟨readFuel, handle, scs, _value, readAfter, checkFuel, repeated, after, stored, _decoded,
    _available, _closed, readExact, _readFrame, checkExact, afterReady, afterPaths, afterRealized,
    afterCounts, afterFlags, _incoming, pending, _continued, orderPreserved, parked, selected, progress⟩ :=
    selected_complete_with_order_progress caller.checked.native.machine.heap before preference uv roots
      safe selection realized paths counts flags
  refine ⟨readFuel, handle, scs, readAfter, checkFuel, repeated, after, stored, readExact, checkExact,
    ⟨roots, afterPaths, afterReady.safe.1, afterRealized, afterCounts, afterFlags⟩,
    afterReady.safe, pending, ?_, selected, progress⟩
  intro repeatedTrue
  obtain ⟨counter, ordered⟩ := orderPreserved repeatedTrue
  obtain ⟨_boundary, _cleared, _disabled, _waiting, resolved, countFuel, _frame, _readRoot,
    _seen, written, indexed⟩ := parked repeatedTrue
  refine ⟨counter, ordered, countFuel, ?_⟩
  intro extra stop order metadata
  apply run_parked_after_write caller.checked.native.machine.heap readFuel checkFuel (countFuel + extra)
    uv handle scs stop order metadata before after readAfter resolved
  · simpa only [Nat.add_zero] using readExact 0
  · simpa only [Nat.add_zero, repeatedTrue] using checkExact 0
  · exact written
  · exact indexed extra

end MicroCFTA.SourcePruningEnumerationParkedRestart
