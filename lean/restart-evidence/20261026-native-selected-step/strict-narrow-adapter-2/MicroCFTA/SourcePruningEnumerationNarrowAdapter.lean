import MicroCFTA.SourcePruningEnumerationNarrowCache

namespace MicroCFTA.SourcePruningEnumerationNarrowAdapter
open EnumerationState EnumerationCorrectness
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Attach the actual narrowing core to unchanged or rebuilt native indexes. -/
def adapt
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : EnumerationState.State Symbol EnumGuard) :
    Option (EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  if newHandle = oldHandle then some (EnumerationExpandableIndex.frame observed before)
  else
    (SourcePruningEnumerationNativeIndex.write heap fuel uv (.unenumerated (some newHandle) scs) scs scs
      (EnumerationExpandableIndex.frame observed before)).map (EnumerationExpandableIndex.frame observed)

/-- Every attached cache retains the exact observed narrowing core. -/
theorem adapt_core
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : EnumerationState.State Symbol EnumGuard)
    (adapted : adapt heap fuel uv oldHandle newHandle scs before observed = some after) :
    after.core = observed := by
  unfold adapt at adapted
  split at adapted
  · cases adapted
    rfl
  · simp only [Option.map_eq_some_iff] at adapted
    obtain ⟨cached, _written, same⟩ := adapted
    subst after
    rfl

/-- The actual replacement write derives the same indexes at its observed endpoint. -/
theorem adapt_after_write
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (resolved observed : EnumerationState.State Symbol EnumGuard)
    (different : newHandle ≠ oldHandle)
    (written : Success (setValue uv (.unenumerated (some newHandle) scs)) resolved () observed)
    (indexed : SourcePruningEnumerationNativeIndex.write heap fuel uv
      (.unenumerated (some newHandle) scs) scs scs (EnumerationExpandableIndex.frame resolved before) = some after)
    (core : after.core = observed) :
    adapt heap fuel uv oldHandle newHandle scs before observed = some after := by
  have shape := (EnumerationDriver.modify_success _ resolved observed).mp written
  have forest : observed.representatives = resolved.representatives := by rw [shape]
  have same : adapt heap fuel uv oldHandle newHandle scs before observed =
      (SourcePruningEnumerationNativeIndex.write heap fuel uv (.unenumerated (some newHandle) scs) scs scs
        (EnumerationExpandableIndex.frame resolved before)).map (EnumerationExpandableIndex.frame observed) := by
    unfold adapt
    rw [ite_eq_right different]
    unfold SourcePruningEnumerationNativeIndex.write
    dsimp only [EnumerationExpandableIndex.frame]
    rw [forest]
    cases SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated (some newHandle) scs) with
    | none => rfl
    | some _flag =>
        cases SourcePruningEnumerationNativeIndex.count fuel resolved.representatives (-1) scs before.waiting with
        | none => rfl
        | some removed =>
            cases SourcePruningEnumerationNativeIndex.count fuel resolved.representatives 1 scs removed <;> rfl
  rw [same, indexed, Option.map_some, ← core]
  rfl

/-- The original narrowing receipt derives sufficient adapter fuel without a future cache premise. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv oldHandle newHandle representativeFuel countFuel : Nat) (scs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (checked : EnumerationState.State Symbol EnumGuard)
    (shape :
      (newHandle = oldHandle ∧ after = EnumerationExpandableIndex.frame checked before) ∨
      (newHandle ≠ oldHandle ∧ ∃ resolved : EnumerationState.State Symbol EnumGuard,
        Success (representative representativeFuel uv) checked uv resolved ∧
        Success (setValue uv (.unenumerated (some newHandle) scs)) resolved () after.core ∧
        ∀ extra, SourcePruningEnumerationNativeIndex.write heap (countFuel + extra) uv
          (.unenumerated (some newHandle) scs) scs scs
          (EnumerationExpandableIndex.frame resolved before) = some after)) :
    ∃ fuel, ∀ extra, adapt heap (fuel + extra) uv oldHandle newHandle scs before after.core = some after := by
  rcases shape with ⟨same, equal⟩ | ⟨different, resolved, _read, written, indexed⟩
  · refine ⟨0, ?_⟩
    intro extra
    rw [adapt, ite_eq_left same, equal]
    rfl
  · refine ⟨countFuel, ?_⟩
    intro extra
    exact adapt_after_write heap (countFuel + extra) uv oldHandle newHandle scs before after
      resolved after.core different written (indexed extra) rfl

end MicroCFTA.SourcePruningEnumerationNarrowAdapter
