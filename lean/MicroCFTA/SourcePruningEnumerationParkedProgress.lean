import MicroCFTA.SourcePruningEnumerationParkedRestart

/-!
# Progress of an actual selected repeated-key park

The actual read and recursion check retain their returned cache.
A repeated key clears one selected bucket and disables its candidate flag.
The allocation counter stays fixed and the candidate list gets shorter.
Later allocating continuations are outside this local progress statement.
-/
namespace MicroCFTA.SourcePruningEnumerationParkedRestart
open EnumerationState EnumerationCorrectness EnumerationSchedule
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {width : Nat}

/-- The actual selected repeated-key branch strictly decreases the finite candidate count. -/
theorem selected_complete_with_parking_progress
    (caller : Caller width) (before : Cached) (preference : List Nat → Option Nat) (uv : Nat)
    (safe : Safe before.core)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (selection : EnumerationPureSelection.next preference before = .expand uv) :
    ∃ (readFuel handle : Nat) (scs : List Suspended) (readAfter : Core)
      (checkFuel : Nat) (repeated : Bool) (after : Cached),
      before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      (∀ extra, ExceptT.run (getValue (readFuel + extra) uv before.core) =
        [.ok (.unenumerated (some handle) scs, readAfter)]) ∧
      (∀ extra, ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap (checkFuel + extra) uv handle scs readAfter) =
        [.ok (repeated, after.core)]) ∧
      SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after ∧ Safe after.core ∧
      (repeated = true → after.core.counter = before.core.counter ∧
        after.expandable = (fun other => if other = uv then false else before.expandable other) ∧
        (EnumerationIndexSelection.candidates after).length <
          (EnumerationIndexSelection.candidates before).length) := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := valid
  obtain ⟨readFuel, handle, scs, _value, readAfter, checkFuel, repeated, after, stored,
    _decoded, _available, _closed, readExact, _readFrame, checkExact, afterReady, afterPaths,
    afterRealized, afterCounts, afterFlags, _incoming, _pending, _continued, ordered, parked⟩ :=
    selected_complete_with_order caller.checked.native.machine.heap before preference uv roots
      safe selection realized paths counts flags
  refine ⟨readFuel, handle, scs, readAfter, checkFuel, repeated, after, stored,
    readExact, checkExact, ⟨roots, afterPaths, afterReady.safe.1, afterRealized, afterCounts, afterFlags⟩,
    afterReady.safe, ?_⟩
  intro repeatedTrue
  obtain ⟨counter, _levels⟩ := ordered repeatedTrue
  obtain ⟨_boundary, _cleared, disabled, _waiting, resolved, _countFuel, frame,
    _readRoot, _seen, written, _indexed⟩ := parked repeatedTrue
  have writtenShape := (EnumerationDriver.modify_success _ resolved after.core).mp written
  have values : after.core.values = before.core.values.set uv (.unenumerated (some handle) []) := by
    simp only [writtenShape, frame.values]
  have flagShape : after.expandable =
      (fun other => if other = uv then false else before.expandable other) := by
    funext other
    by_cases same : other = uv
    · subst other
      simp only [disabled, ↓reduceIte]
    · have observed := afterFlags other
      rw [values, List.getElem?_set_ne (Ne.symm same)] at observed
      have sameFlag : before.expandable other = after.expandable other :=
        Option.some.inj ((flags other).symm.trans observed)
      simpa only [ite_eq_right same] using sameFlag.symm
  obtain ⟨inside, enabled, _unblocked⟩ :=
    SourcePruningEnumerationSelection.offered before preference uv selection
  have member : uv ∈ EnumerationIndexSelection.candidates before :=
    List.mem_filter.mpr ⟨List.mem_range.mpr inside, enabled⟩
  have filtered : EnumerationIndexSelection.candidates after =
      (EnumerationIndexSelection.candidates before).filter (fun other => decide (other ≠ uv)) := by
    unfold EnumerationIndexSelection.candidates
    rw [counter, flagShape, List.filter_filter]
    apply List.filter_congr
    intro other _member
    by_cases same : other = uv <;> simp [same]
  have bounded : (EnumerationIndexSelection.candidates after).length ≤
      (EnumerationIndexSelection.candidates before).length := by
    rw [filtered]
    exact List.length_filter_le _ _
  have unequal : (EnumerationIndexSelection.candidates after).length ≠
      (EnumerationIndexSelection.candidates before).length := by
    intro equalLength
    rw [filtered] at equalLength
    have impossible := (List.length_filter_eq_length_iff.mp equalLength) uv member
    simp at impossible
  exact ⟨counter, flagShape, by omega⟩

end MicroCFTA.SourcePruningEnumerationParkedRestart
