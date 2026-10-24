import MicroCFTA.SourcePruningEnumerationNodes
import MicroCFTA.EnumerationNodeObservation

/-!
# Actual pending-node observations from realized slots

Initial closed values derive their stored model handles. Actual observations
retain the compression frame and derive the complete available node record.
Storage bounds supply finite observations and persist through actual reads.
Slot-write producers and native representation correspondence remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationObservation
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame EnumerationObservations
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Each stored pending handle decodes to a closed available interned value. -/
def PendingRealized (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : EnumerationState.State Symbol EnumGuard) : Prop :=
  ∀ (slot node : Nat) (scs : List EnumerationState.Suspended),
    state.values[slot]? = some (.unenumerated (some node) scs) →
      ∃ value : InternedConstructorTemplates.Value Symbol NativeGuard,
        lookupNode heap node = some value ∧
        InternedProbeProvenance.Available heap value ∧ value.free = []

/-- A closed available input derives the handle in the actual initial slot. -/
theorem initial_realized (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = []) :
    ∃ node, encodeNode value = some node ∧
      PendingRealized heap (EnumerationState.initial node : EnumerationState.State Symbol EnumGuard) := by
  obtain ⟨node, encoded, decoded⟩ := available_readback heap value coherent available closed
  refine ⟨node, encoded, ?_⟩
  intro slot storedNode scs stored
  cases slot with
  | zero =>
      simp [EnumerationState.initial] at stored
      obtain ⟨rfl, rfl⟩ := stored
      exact ⟨value, decoded, available, closed⟩
  | succ => simp [EnumerationState.initial] at stored

/-- A full enumeration frame and actual native growth retain realized slots. -/
theorem realized_preserved (heap nextHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationState.State Symbol EnumGuard)
    (realized : PendingRealized heap before) (frame : Frame before after)
    (kept : SourceEqualityRequiredCache.Keeps heap nextHeap) : PendingRealized nextHeap after := by
  intro slot node scs stored
  have earlierStored : before.values[slot]? = some (.unenumerated (some node) scs) := by
    simpa only [frame.values] using stored
  obtain ⟨value, decoded, available, closed⟩ := realized slot node scs earlierStored
  exact ⟨value, lookupNode_keeps heap nextHeap kept node value decoded,
    available.grows heap nextHeap kept.growth kept.history, closed⟩

/-- An actual pending-node read derives its complete available closed value. -/
theorem observed_realized (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv node : Nat) (before after : EnumerationState.State Symbol EnumGuard)
    (realized : PendingRealized heap before) (total : UnionFind.Total before.representatives)
    (observed : Success (getUnexpandedNode fuel uv) before (some node) after) :
    Frame before after ∧
      ∃ value : InternedConstructorTemplates.Value Symbol NativeGuard,
        lookupNode heap node = some value ∧
        InternedProbeProvenance.Available heap value ∧ value.free = [] := by
  obtain ⟨storedValue, valueRead, projected⟩ :=
    (getUnexpandedNode_success fuel uv before after (some node)).mp observed
  have frame : Frame before after := (getValue_frame fuel uv before after storedValue total valueRead).1
  obtain ⟨found, _lookup, stored, _afterSame⟩ := (getValue_success fuel uv before after storedValue).mp valueRead
  refine ⟨frame, ?_⟩
  cases storedValue with
  | enumerated | eliminated => cases projected
  | unenumerated pending scs =>
      cases pending with
      | none => cases projected
      | some pendingNode =>
          cases Option.some.inj projected
          exact realized found.representative node scs stored

/-- An actual allocated observation retains the storage premises for later reads. -/
theorem observation_storage (fuel uv : Nat) (before after : EnumerationState.State Symbol EnumGuard)
    (node : Option Nat) (storage : StorageValid before) (inside : uv < before.counter)
    (observed : Success (getUnexpandedNode fuel uv) before node after) : StorageValid after := by
  obtain ⟨storedValue, valueRead, _projected⟩ := (getUnexpandedNode_success fuel uv before after node).mp observed
  obtain ⟨found, lookup, _stored, rfl⟩ := (getValue_success fuel uv before after storedValue).mp valueRead
  exact representative_storage before storage fuel uv inside found lookup

/-- Storage and an allocated raw variable derive an actual finite observation. -/
theorem observation_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationState.State Symbol EnumGuard) (uv : Nat)
    (realized : PendingRealized heap before)
    (storage : StorageValid before) (inside : uv < before.counter) :
    ∃ fuel observed after,
      Success (getUnexpandedNode fuel uv) before observed after ∧ Frame before after ∧
      (∀ node, observed = some node →
        ∃ value : InternedConstructorTemplates.Value Symbol NativeGuard,
          lookupNode heap node = some value ∧
          InternedProbeProvenance.Available heap value ∧ value.free = []) := by
  obtain ⟨root, size, path⟩ := storage.total uv
  obtain ⟨fuel, found, lookup⟩ := UnionFind.findRoot_terminates path
  have rootInside : found.representative < before.counter :=
    (findRoot_bounded fuel before.representatives before.counter uv storage.forest inside found lookup).1
  have listInside : found.representative < before.values.length := by
    rw [← storage.aligned]
    exact rootInside
  let storedValue : UVarValue Symbol := before.values[found.representative]'listInside
  have stored : before.values[found.representative]? = some storedValue := List.getElem?_eq_getElem listInside
  let after : EnumerationState.State Symbol EnumGuard := {before with representatives := found.forest}
  let observed : Option Nat := match storedValue with | .unenumerated pending _ => pending | _ => none
  have valueRead : Success (getValue fuel uv) before storedValue after :=
    (getValue_success fuel uv before after storedValue).mpr ⟨found, lookup, stored, rfl⟩
  have nodeRead : Success (getUnexpandedNode fuel uv) before observed after :=
    (getUnexpandedNode_success fuel uv before after observed).mpr
      ⟨storedValue, valueRead, by cases storedValue <;> rfl⟩
  have frame : Frame before after := (getValue_frame fuel uv before after storedValue storage.total valueRead).1
  refine ⟨fuel, observed, after, nodeRead, frame, ?_⟩
  intro node same
  rw [same] at nodeRead
  exact (observed_realized heap fuel uv node before after realized storage.total nodeRead).2

end MicroCFTA.SourcePruningEnumerationObservation
