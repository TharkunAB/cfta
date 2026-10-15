import MicroCFTA.SourceEqualityEditExecution
import MicroCFTA.SourceClosedSelfHeadRepair

/-!
# Kernel checks for edit branch priority and retained raw cycles

The complete worker distinguishes node leaves from list leaves, preserves
signed missing-position behavior, and resolves the actual closed self binder.
No native evaluation axiom is used.
-/
namespace MicroCFTA.SourceEqualityEditExamples
open InternedConstructorTemplates InternedNestedConstruction
open SourceEqualityEdits SourceEqualityEditGraph SourceEqualityEditWorker

/-- A callback with a visible failure shows precisely whether the source invokes it. -/
def fails : Callback Unit Nat Unit := fun _ _ state => .unresolved .depth state

/-- Node leaves execute before empty/reference checks, while child-list leaves are ignored. -/
theorem leaf_priority (state : State Nat Unit) :
    edit fails 1 0 (.editAt ()) .empty state = .unresolved .depth state ∧
    edit fails 1 0 (.editAt ()) (.reference .depth) state = .unresolved .depth state ∧
    editAll fails 0 0 [([], ())] [.reference .depth] state = .done [.reference .depth] state := by
  constructor
  · rfl
  · constructor <;> rfl

/-- Negative and high signed positions do not invoke their callback or create a slot. -/
theorem missing_positions (state : State Nat Unit) :
    editAll fails 0 0 [([-1], ()), ([9], ())] [.reference .depth] state = .done [.reference .depth] state := rfl

/-- Observe actual raw-cycle head normalization and both independent proof bounds. -/
def SelfResults : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending _ _ => False
  | .done value state =>
      edit fails 2 2 (.editBelow []) value state = .done .empty state ∧
      edit fails 1 2 (.editBelow []) value state = .exhausted .worker state ∧
      edit fails 2 1 (.editBelow []) value state = .exhausted .head state ∧
      editAll fails 0 0 [([], ())] [value] state = .done [value] state

/-- Even an empty below-edit normalizes a node head; a root list leaf does not visit it. -/
theorem raw_self : SelfResults
    (InternedFreshOrdinaryConstruction.build SourceClosedSelfRequireBoundary.expression [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in
    cbv

end MicroCFTA.SourceEqualityEditExamples
