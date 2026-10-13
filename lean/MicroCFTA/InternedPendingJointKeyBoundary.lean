import MicroCFTA.InternedOrdinaryCaptureBoundary

/-!
# The ordinary-alias fixture has different actual key components

The inner level aliases an original live ordinary capture. Both actual
inner probe references nevertheless differ from the ancestor's original
probe references. The fixture does not satisfy the joint-key premise of
the hypothetical pending site.
-/
namespace MicroCFTA.InternedPendingJointKeyBoundary
open InternedConstructorTemplates InternedOrdinaryCaptureBoundary

/-- Compare the actual inner probe pair with the original ancestor pair. -/
def differences : Value Symbol Guard → Option (Bool × Bool)
  | .mu _ (.union _ (.mu _ _ innerDepth innerOrdinary :: _) _ _) outerDepth outerOrdinary =>
      some (decide (innerDepth.referenceOf ≠ outerDepth.referenceOf),
        decide (innerOrdinary.referenceOf ≠ outerOrdinary.referenceOf))
  | _ => none

/-- Read both comparisons from the actual stored ancestor at slot 93. -/
def selectedDifferences : Option (Bool × Bool) := do
  let key ← result.state.nodes.issued 93
  let value ← result.state.nodeRecords key
  differences value

/-- The completed closed alias fixture differs in both exact key components. -/
theorem closed_different_pairs : selectedDifferences = some (true, true) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 100000000 in cbv

end MicroCFTA.InternedPendingJointKeyBoundary
