import MicroCFTA.SourcePruningEnumerationIsolatedPrefixOperations

/-!
# Isolation from the actual existing-slot clear

A repeated check clears an existing root. It does not allocate that root.
The actual write retains the native handle and removes only the bucket.
-/
namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationSchedule EnumerationReferences
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard : Type}

/-- An actual clear isolates an existing root with no incoming suspended reference. -/
theorem cleared_isolated (uv handle : Nat) (before after : EnumerationState.State Symbol EnumGuard)
    (inside : uv < before.values.length) (root : IsRoot before.representatives uv)
    (incoming : IncomingAvoid uv before)
    (written : Success (setValue uv (.unenumerated (some handle) [])) before () after) :
    IsolatedPending uv handle after := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  refine ⟨?_, ?_, EnumerationPendingReplacement.setValue_clear_incoming
    uv uv (some handle) before after incoming written⟩
  · simpa only [shape] using root
  · simpa only [shape, List.getElem?_set_self inside]

end MicroCFTA.EnumerationDischargeHistory
