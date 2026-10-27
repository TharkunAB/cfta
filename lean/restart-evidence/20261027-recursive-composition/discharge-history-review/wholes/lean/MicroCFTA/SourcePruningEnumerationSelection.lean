import MicroCFTA.SourcePruningEnumerationNativeIndex
import MicroCFTA.EnumerationReferences

namespace MicroCFTA.SourcePruningEnumerationSelection
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Pure selection returns an allocated candidate with no waiting entry. -/
theorem offered
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat)
    (selected : EnumerationPureSelection.next preference before = .expand uv) :
    uv < before.core.counter ∧ before.expandable uv = true ∧ before.waiting uv = none := by
  dsimp only [EnumerationPureSelection.next, EnumerationPureSelection.find] at selected
  split at selected
  · cases selected
  · have member := pickNext_safe preference _ uv selected
    obtain ⟨candidate, unblocked⟩ := List.mem_filter.mp member
    obtain ⟨inside, flag⟩ := List.mem_filter.mp candidate
    exact ⟨List.mem_range.mp inside, flag, Option.isNone_iff_eq_none.mp unblocked⟩

/-- Exact waiting counts separate an unblocked root from every stored reference. -/
theorem unblocked_avoids
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (held : Nat) (root : IsRoot before.core.representatives held)
    (unblocked : before.waiting held = none)
    (slot : Nat) (node : Option Nat) (scs : List Suspended)
    (stored : before.core.values[slot]? = some (.unenumerated node scs)) :
    Avoids before.core.representatives held scs := by
  intro sc member same
  have fixed : roots held = held := (root_iff _ roots paths held).mp root
  have named : roots sc.var = held :=
    ((class_iff _ roots paths held sc.var).mp same).symm.trans fixed
  have blocked := (EnumerationCanonicalWaiting.support_exact
    roots before.core.values before.waiting counts held).mpr
      ⟨.unenumerated node scs, List.mem_iff_getElem?.mpr ⟨slot, stored⟩, sc, member, named⟩
  exact blocked unblocked

/-- Native flags and canonical counts derive the caller's safe expansion precondition. -/
theorem ready
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat)
    (safe : Safe before.core)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (selected : EnumerationPureSelection.next preference before = .expand uv) :
    EnumerationDriver.Ready uv before.core := by
  obtain ⟨inside, flag, unblocked⟩ := offered before preference uv selected
  have insideValues : uv < before.core.values.length := by
    rw [← safe.1.aligned]
    exact inside
  have stored : before.core.values[uv]? = some before.core.values[uv] :=
    List.getElem?_eq_getElem insideValues
  have nativeFlag : SourcePruningEnumerationNativeIndex.candidate heap before.core.values[uv] =
      some true := by
    simpa only [stored, Option.getD_some, flag] using flags uv
  have live : before.core.values[uv] ≠ .eliminated := by
    intro eliminated
    simp only [eliminated, SourcePruningEnumerationNativeIndex.candidate] at nativeFlag
    cases nativeFlag
  have root : IsRoot before.core.representatives uv := (safe.2 uv _ stored).mp live
  exact ⟨safe, inside, root, fun node scs read =>
    unblocked_avoids before roots paths counts uv root unblocked uv (some node) scs read⟩

/-- An unblocked root has no stored incoming suspended reference. -/
theorem unblocked_incoming
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (uv : Nat) (root : IsRoot before.core.representatives uv)
    (unblocked : before.waiting uv = none) : EnumerationReferences.IncomingAvoid uv before.core := by
  intro value member
  cases value with
  | eliminated | enumerated _ => simp [references, EnumerationReferences.InputsAllowed]
  | unenumerated node scs =>
    obtain ⟨slot, stored⟩ := List.mem_iff_getElem?.mp member
    exact unblocked_avoids before roots paths counts uv root unblocked slot node scs stored

/-- Actual native selection derives the absence of incoming references at the same cache. -/
theorem incoming
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat) (safe : Safe before.core)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (selected : EnumerationPureSelection.next preference before = .expand uv) :
    EnumerationReferences.IncomingAvoid uv before.core :=
  unblocked_incoming before roots paths counts uv
    (ready heap before preference uv safe roots paths counts flags selected).root
    (offered before preference uv selected).2.2

/-- A selected native candidate has its actual closed available pending value. -/
theorem realized
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat)
    (aligned : before.core.counter = before.core.values.length)
    (pending : PendingRealized heap before.core)
    (flags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (selected : EnumerationPureSelection.next preference before = .expand uv) :
    ∃ (node : Nat) (scs : List Suspended)
      (value : InternedConstructorTemplates.Value Symbol NativeGuard),
      before.core.values[uv]? = some (.unenumerated (some node) scs) ∧
      lookupNode heap node = some value ∧
      InternedProbeProvenance.Available heap value ∧ value.free = [] ∧
      (!(MergedOrdinaryHeight.recursiveBoundary value && scs.isEmpty)) = true := by
  obtain ⟨inside, flag, _unblocked⟩ := offered before preference uv selected
  have insideValues : uv < before.core.values.length := by
    rw [← aligned]
    exact inside
  have stored : before.core.values[uv]? = some before.core.values[uv] :=
    List.getElem?_eq_getElem insideValues
  have nativeFlag : SourcePruningEnumerationNativeIndex.candidate heap before.core.values[uv] =
      some true := by
    simpa only [stored, Option.getD_some, flag] using flags uv
  cases slotValue : before.core.values[uv] with
  | eliminated | enumerated _ =>
    simp only [slotValue, SourcePruningEnumerationNativeIndex.candidate] at nativeFlag
    cases nativeFlag
  | unenumerated node scs =>
    rw [slotValue] at stored nativeFlag
    cases node with
    | none =>
      simp only [SourcePruningEnumerationNativeIndex.candidate] at nativeFlag
      cases nativeFlag
    | some node =>
      obtain ⟨value, decoded, available, closed⟩ := pending uv node scs stored
      refine ⟨node, scs, value, stored, decoded, available, closed, ?_⟩
      simpa only [SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some,
        Option.some.injEq] using nativeFlag

end MicroCFTA.SourcePruningEnumerationSelection
