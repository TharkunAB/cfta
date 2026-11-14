import MicroCFTA.SourcePruningEnumerationAction
import MicroCFTA.SourcePruningEnumerationNodes

namespace MicroCFTA.SourceCurrentMuPrepareResources

open EnumerationState InternedConstructorTemplates

attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- Prepare an original Mu value with no native fuel or heap change.
This creation draft is UNCOMPILED. It does not establish a finite key carrier. -/
theorem mu_prepare
    {NativeGuard EnumGuard Typing Key : Type}
    [DecidableEq (EdgeKey SourcePruningTemplates.Symbol NativeGuard)]
    (holeKey : Typing → Nat → Key) (fits : Key → SourcePruningTemplates.Symbol → Bool)
    (admits : Key → Value SourcePruningTemplates.Symbol NativeGuard → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (uv oldHandle : Nat) (scs : List Suspended)
    (value : Value SourcePruningTemplates.Symbol NativeGuard) (heap : InternedConstructorTemplates.State SourcePruningTemplates.Symbol NativeGuard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value)
    (closed : value.free = [])
    (mu : match value with | .mu .. => True | _ => False) :
    ∃ newHandle,
      SourcePruningEnumerationNodes.encodeNode value = some newHandle ∧
      SourcePruningEnumerationNodes.lookupNode heap newHandle = some value ∧
      ∀ nativeFuel representativeFuel,
        SourcePruningEnumerationAction.prepare holeKey fits admits metadata
          nativeFuel representativeFuel uv oldHandle scs value heap =
        MergedSourceComparison.Result.done
          ((value, some (if newHandle = oldHandle then pure () else
            representative representativeFuel uv >>= fun target =>
              setValue target (.unenumerated (some newHandle) scs))) :
            Value SourcePruningTemplates.Symbol NativeGuard × Option (EnumerateM SourcePruningTemplates.Symbol EnumGuard Unit)) heap := by
  obtain ⟨newHandle, encoded, readback⟩ :=
    SourcePruningEnumerationNodes.available_readback heap value coherent available closed
  refine ⟨newHandle, encoded, readback, ?_⟩
  cases value with
  | empty => cases mu
  | reference => cases mu
  | node _ _ _ _ => cases mu
  | union _ _ _ _ => cases mu
  | mu _ _ _ _ =>
      intro nativeFuel representativeFuel
      simp only [SourcePruningEnumerationAction.prepare, SourcePruningEnumerationAction.prepareWithNarrow,
        SourcePruningOuterNarrow.narrow, encoded]

end MicroCFTA.SourceCurrentMuPrepareResources
