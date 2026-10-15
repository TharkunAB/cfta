import MicroCFTA.SourceEqualitySelectionEntry

/-!
# A closed raw self binder reaches the next required-path boundary

Actual repaired construction retains this exported raw binder. The gate
clears every path because the binder is closed and unconstrained. Actual
unfolding returns the same binder and cache. The source requireNode Mu
branch therefore cannot use the open-Mu rank to justify progress here.
-/
namespace MicroCFTA.SourceClosedSelfRequireBoundary
open InternedConstructorTemplates InternedNestedConstruction

/-- The source raw constructor retains its own bare recursive reference. -/
def expression : Syntax Nat Unit := .binder false (.var 0)

/-- Observe actual construction, the clear gate, and exact stored unfolding stutter. -/
def Stutters : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending _ _ => False
  | .done value state =>
      match value with
      | .mu .. => value.free = [] ∧
          InternedSourceCrush.unconstrained (fun _ : Unit => true) value = true ∧
          InternedFreshOrdinaryStoredSubstitution.unfold value state = .done value state ∧
          ∀ path, InternedFreshOrdinaryStatefulGate.nodeMeets
            (InternedSourceCrush.unconstrained (fun _ : Unit => true)) 1 path value state = .done (some false) state
      | _ => False

/-- Kernel evaluation confirms this boundary in the actual repaired source executor. -/
theorem actual_stutter : Stutters (InternedFreshOrdinaryConstruction.build expression [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in
    cbv
    intro path
    cbv

end MicroCFTA.SourceClosedSelfRequireBoundary
