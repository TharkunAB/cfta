import MicroCFTA.SourcePruningEnumerationRecursionOrder
import MicroCFTA.EnumerationPendingOrder

namespace MicroCFTA.SourcePruningEnumerationPrefixHistory
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Actual prefix reads and a pending replacement retain the counter and dependency order.
Initial safety supplies read totality. No safety result follows from a frame alone. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (readAfter checked : EnumerationState.State Symbol EnumGuard)
    (readFuel checkFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (safe : EnumerationSchedule.Safe before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some oldHandle) scs))
    (read : Success (getValue readFuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter)
    (check : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv oldHandle scs)
      readAfter false checked)
    (shape : after = EnumerationExpandableIndex.frame checked before ∨
      ∃ resolved : EnumerationState.State Symbol EnumGuard,
        Success (representative representativeFuel uv) checked uv resolved ∧
        Success (setValue uv (.unenumerated (some newHandle) scs)) resolved () after.core) :
    after.core.counter = before.core.counter ∧
      ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
        EnumerationOrder.Stratified after.core level frontier := by
  have readFrame := (getValue_frame readFuel uv before.core readAfter _ safe.1.total read).1
  have checkedFrame := readFrame.trans
    (SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame heap checkFuel uv oldHandle scs
      readAfter checked (readFrame.total safe.1.total) check)
  rcases shape with equal | ⟨resolved, reading, written⟩
  · refine ⟨?_, ?_⟩
    · simpa only [equal, EnumerationExpandableIndex.frame] using checkedFrame.counter
    · intro level frontier ordered
      simpa only [equal, EnumerationExpandableIndex.frame] using
        EnumerationOrder.frame_stratified before.core checked checkedFrame level frontier ordered
  · have resolvedFrame := representative_frame representativeFuel uv uv checked resolved
      (checkedFrame.total safe.1.total) reading
    have wholeFrame := checkedFrame.trans resolvedFrame
    have writtenShape := (EnumerationDriver.modify_success _ resolved after.core).mp written
    have oldStored : resolved.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
      simpa only [wholeFrame.values] using stored
    refine ⟨?_, ?_⟩
    · simpa only [writtenShape] using wholeFrame.counter
    · intro level frontier ordered
      exact EnumerationOrder.setValue_pending_stratified uv (some oldHandle) (some newHandle) scs scs
        resolved after.core oldStored level frontier
        (EnumerationOrder.frame_stratified before.core resolved wholeFrame level frontier ordered) written

end MicroCFTA.SourcePruningEnumerationPrefixHistory
