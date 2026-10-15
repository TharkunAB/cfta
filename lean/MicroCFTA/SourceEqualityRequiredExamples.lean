import MicroCFTA.SourceEqualityRequiredExecution
import MicroCFTA.SourceClosedSelfHeadRepair

/-!
# Kernel checks for required-path control and retained raw cycles

The examples use actual repaired source construction and the complete worker.
They distinguish the two proof bounds and retain the source's early row
rejection before an unresolved child request.
-/
namespace MicroCFTA.SourceEqualityRequiredExamples
open InternedConstructorTemplates InternedNestedConstruction
open SourceEqualityRequiredWorker

/-- Observe successful empty-cycle traversal and each independent exhausted bound. -/
def SelfResults : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending _ _ => False
  | .done value state =>
      require 2 2 (SourceEqualityNeeded.build [[0]]) value state = .done .empty state ∧
      require 1 2 (SourceEqualityNeeded.build [[0]]) value state = .exhausted .worker state ∧
      require 2 1 (SourceEqualityNeeded.build [[0]]) value state = .exhausted .head state

/-- The complete repaired source worker resolves the exported raw self binder. -/
theorem raw_self : SelfResults
    (InternedFreshOrdinaryConstruction.build SourceClosedSelfRequireBoundary.expression [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in
    cbv

/-- One source edge contains a bare open recursive reference at its first child. -/
def openExpression : Syntax Nat Unit := .node [.mk 0 () [.var 0]]

/-- A rejected row avoids its open child; a retained deeper request reports that exact reference. -/
def OpenResults : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending _ _ => False
  | .done value state =>
      require 1 0 (SourceEqualityNeeded.build [[1]]) value state = .done .empty state ∧
      require 2 0 (SourceEqualityNeeded.build [[0, 0]]) value state = .unresolved .depth state

/-- The actual row arity check occurs before child traversal and edge reconstruction. -/
theorem reject_before_child : OpenResults
    (InternedFreshOrdinaryConstruction.build openExpression [.reference .depth] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in
    cbv

end MicroCFTA.SourceEqualityRequiredExamples
