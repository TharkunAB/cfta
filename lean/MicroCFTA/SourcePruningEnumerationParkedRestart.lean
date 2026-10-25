import MicroCFTA.SourcePruningEnumerationRecursion
import MicroCFTA.EnumerationPendingOrder
import MicroCFTA.SourcePruningEnumerationRestart

namespace MicroCFTA.SourcePruningEnumerationParkedRestart
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- The actual pending-bucket clear retains the allocation counter and dependency levels. -/
theorem parked_order
    (uv handle : Nat) (scs : List Suspended)
    (before resolved after : EnumerationState.State Symbol EnumGuard)
    (stored : before.values[uv]? = some (.unenumerated (some handle) scs))
    (frame : Frame before resolved)
    (written : Success (setValue uv (.unenumerated (some handle) [])) resolved () after) :
    after.counter = before.counter ∧
    ∀ level frontier, EnumerationOrder.Stratified before level frontier →
      EnumerationOrder.Stratified after level frontier := by
  have resolvedStored : resolved.values[uv]? = some (.unenumerated (some handle) scs) := by
    simpa only [frame.values] using stored
  have shape := (EnumerationDriver.modify_success _ resolved after).mp written
  refine ⟨?_, ?_⟩
  · simpa only [shape] using frame.counter
  · intro level frontier stratified
    exact EnumerationOrder.setValue_pending_stratified uv (some handle) (some handle) scs []
      resolved after resolvedStored level frontier
      (EnumerationOrder.frame_stratified before resolved frame level frontier stratified) written

/-- Original selection retains its actual recursion receipts and the parked dependency order. -/
theorem selected_complete_with_order
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
            (.unenumerated (some handle) []) [] scs (EnumerationExpandableIndex.frame resolved before) = some after) := by
  obtain ⟨readFuel, handle, scs, value, readAfter, checkFuel, repeated, after, stored, decoded,
    available, closed, readExact, readFrame, checkExact, afterReady, afterPaths, afterRealized,
    afterCounts, afterFlags, incoming, pending, continued, parked⟩ :=
    SourcePruningEnumerationRecursion.selected_complete heap before preference uv roots
      safe selection realized paths counts flags
  refine ⟨readFuel, handle, scs, value, readAfter, checkFuel, repeated, after, stored, decoded,
    available, closed, readExact, readFrame, checkExact, afterReady, afterPaths, afterRealized,
    afterCounts, afterFlags, incoming, pending, continued, ?_, parked⟩
  intro repeatedTrue
  obtain ⟨_boundary, _cleared, _disabled, _waiting, resolved, _countFuel, frame, _readRoot,
    _seen, written, _indexed⟩ := parked repeatedTrue
  exact parked_order uv handle scs before.core resolved after.core stored frame written

local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {width : Nat}

/-- Rebuild the cleared slot's flag and remove its original suspended counts. -/
def adapt
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (indexFuel uv handle : Nat) (scs : List Suspended)
    (before : Cached) (checked : EnumerationState.State Symbol Constraint) : Option Cached :=
  (SourcePruningEnumerationNativeIndex.write heap indexFuel uv (.unenumerated (some handle) []) [] scs
    (EnumerationExpandableIndex.frame checked before)).map (EnumerationExpandableIndex.frame checked)

/-- An attached parked cache retains the exact observed check endpoint. -/
theorem adapt_core
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (indexFuel uv handle : Nat) (scs : List Suspended)
    (before after : Cached) (checked : EnumerationState.State Symbol Constraint)
    (adapted : adapt heap indexFuel uv handle scs before checked = some after) :
    after.core = checked := by
  simp only [adapt, Option.map_eq_some_iff] at adapted
  obtain ⟨cached, _written, same⟩ := adapted
  subst after
  rfl

/-- The actual clear write supplies the same rebuilt parked cache after observation. -/
theorem adapt_after_write
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (indexFuel uv handle : Nat) (scs : List Suspended)
    (before after : Cached) (resolved checked : EnumerationState.State Symbol Constraint)
    (written : Success (setValue uv (.unenumerated (some handle) [])) resolved () checked)
    (indexed : SourcePruningEnumerationNativeIndex.write heap indexFuel uv
      (.unenumerated (some handle) []) [] scs (EnumerationExpandableIndex.frame resolved before) = some after)
    (core : after.core = checked) :
    adapt heap indexFuel uv handle scs before checked = some after := by
  have shape := (EnumerationDriver.modify_success _ resolved checked).mp written
  have forest : checked.representatives = resolved.representatives := by rw [shape]
  have same : adapt heap indexFuel uv handle scs before checked =
      (SourcePruningEnumerationNativeIndex.write heap indexFuel uv (.unenumerated (some handle) []) [] scs
        (EnumerationExpandableIndex.frame resolved before)).map (EnumerationExpandableIndex.frame checked) := by
    unfold adapt SourcePruningEnumerationNativeIndex.write
    dsimp only [EnumerationExpandableIndex.frame]
    rw [forest]
    cases SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated (some handle) []) with
    | none => rfl
    | some _flag =>
        cases SourcePruningEnumerationNativeIndex.count indexFuel resolved.representatives (-1) scs before.waiting <;> rfl
  rw [same, indexed, Option.map_some, ← core]
  rfl

/-- Read and check once, then restart with rebuilt indexes on the repeated branch. -/
def run
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (readFuel checkFuel indexFuel uv : Nat)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached) : EnumerateM Symbol Constraint (Option (Metadata Typing × Option Next)) :=
  fun state =>
    (ExceptT.run (getValue readFuel uv state)).flatMap fun row =>
      match row with
      | .error error => [.error error]
      | .ok (.unenumerated (some handle) scs, readAfter) =>
          (ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv handle scs readAfter)).flatMap
            fun checkedRow => match checkedRow with
            | .error error => [.error error]
            | .ok (false, checked) => [.ok (none, checked)]
            | .ok (true, checked) =>
                match adapt heap indexFuel uv handle scs before checked with
                | none => [.error .representativeFuel]
                | some parked =>
                    (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked)).map
                      fun restarted => match restarted with
                      | .error error => .error error
                      | .ok (result, final) => .ok (some result, final)
      | .ok _ => []

/-- Actual read, check and index observations derive the exact parked restart result. -/
theorem run_parked
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (readFuel checkFuel indexFuel uv handle : Nat) (scs : List Suspended)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before parked : Cached) (readAfter checked : EnumerationState.State Symbol Constraint)
    (read : ExceptT.run (getValue readFuel uv before.core) =
      [.ok (.unenumerated (some handle) scs, readAfter)])
    (check : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv handle scs readAfter) =
      [.ok (true, checked)])
    (adapted : adapt heap indexFuel uv handle scs before checked = some parked) :
    ExceptT.run (run heap readFuel checkFuel indexFuel uv stop order metadata before before.core) =
      if SourcePruningEnumerationRestart.decision stop order metadata parked = some .stuck then []
      else [.ok (some (metadata, SourcePruningEnumerationRestart.decision stop order metadata parked), parked.core)] := by
  have core := adapt_core heap indexFuel uv handle scs before parked checked adapted
  rw [core]
  simp only [run, read, check, List.flatMap_singleton, adapted, SourcePruningEnumerationRestart.run]
  split <;> rfl

/-- The selected producer's actual clear and indexed-write receipts discharge cache recovery. -/
theorem run_parked_after_write
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (readFuel checkFuel indexFuel uv handle : Nat) (scs : List Suspended)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before parked : Cached) (readAfter resolved : EnumerationState.State Symbol Constraint)
    (read : ExceptT.run (getValue readFuel uv before.core) =
      [.ok (.unenumerated (some handle) scs, readAfter)])
    (check : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv handle scs readAfter) =
      [.ok (true, parked.core)])
    (written : Success (setValue uv (.unenumerated (some handle) [])) resolved () parked.core)
    (indexed : SourcePruningEnumerationNativeIndex.write heap indexFuel uv
      (.unenumerated (some handle) []) [] scs (EnumerationExpandableIndex.frame resolved before) = some parked) :
    ExceptT.run (run heap readFuel checkFuel indexFuel uv stop order metadata before before.core) =
      if SourcePruningEnumerationRestart.decision stop order metadata parked = some .stuck then []
      else [.ok (some (metadata, SourcePruningEnumerationRestart.decision stop order metadata parked), parked.core)] := by
  exact run_parked heap readFuel checkFuel indexFuel uv handle scs stop order metadata before parked
    readAfter parked.core read check
    (adapt_after_write heap indexFuel uv handle scs before parked resolved parked.core written indexed rfl)

/-- Original native selection derives the indexed parked restart without a future cache premise. -/
theorem selected_complete_with_restart
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
            else [.ok (some (metadata, SourcePruningEnumerationRestart.decision stop order metadata after), after.core)]) := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := valid
  obtain ⟨readFuel, handle, scs, _value, readAfter, checkFuel, repeated, after, stored, _decoded,
    _available, _closed, readExact, _readFrame, checkExact, afterReady, afterPaths, afterRealized,
    afterCounts, afterFlags, _incoming, pending, _continued, orderPreserved, parked⟩ :=
    selected_complete_with_order caller.checked.native.machine.heap before preference uv roots
      safe selection realized paths counts flags
  refine ⟨readFuel, handle, scs, readAfter, checkFuel, repeated, after, stored, readExact, checkExact,
    ⟨roots, afterPaths, afterReady.safe.1, afterRealized, afterCounts, afterFlags⟩,
    afterReady.safe, pending, ?_⟩
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
