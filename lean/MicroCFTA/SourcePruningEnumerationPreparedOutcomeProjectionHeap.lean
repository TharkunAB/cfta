import MicroCFTA.SourcePruningEnumerationPreparedOutcomeResources
import MicroCFTA.SourcePruningEnumerationConstraint

/-!
# Projectability at actual prepared recursive returns

The aggregate caller remains explicit when the output list is empty.
Each output retains its own native caller.
An absent stopped endpoint supplies no caller.
The existing resource certificate remains a separate requirement.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Output)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Retain projection at the actual aggregate endpoint and each emitted output caller. -/
def OutcomeProjectionHeap
    (outcome : SourcePruningEnumerationNativeContinuations.HookResult
      (Output width Typing) (Failure width Typing) width) : Prop :=
  match outcome with
  | .complete outputs caller _ =>
      ProjectionHeap caller.checked.native.machine.heap ∧
      ∀ output ∈ outputs, ProjectionHeap output.caller.checked.native.machine.heap
  | .stopped outputs _ endpoint =>
      (match endpoint with
      | none => True
      | some (caller, _) => ProjectionHeap caller.checked.native.machine.heap) ∧
      ∀ output ∈ outputs, ProjectionHeap output.caller.checked.native.machine.heap

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
