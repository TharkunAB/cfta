import MicroCFTA.SourceEqualityPartialChecks

/-!
# Recursive child graphs from actual checked callback receipts

The smaller-call premise applies only at checked child entries. It supplies
an actual node graph, not a language law. Indexed traversal retains the
descended payload and the full returned native state.
-/
namespace MicroCFTA.SourceEqualityPartialLiftChildren
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityPartialGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Checked successful child receipts give the exact recursive indexed graph. -/
theorem walk {width : Nat}
    {call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → SourceEqualityPartialWorker.Result width}
    {check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Prop}
    (node : ∀ inherited value before result after, check inherited value before →
      call inherited value before = .done (.ok result) after → ReduceNode inherited value before result after)
    {payload index values before results after}
    (trace : SourceEqualityInheritedChildren.Walk call payload index values before results after)
    (plan : SourceEqualityPartialChecks.Walk call check payload index values before) :
    WalkChildren payload index values before results after := by
  induction trace with
  | nil => exact .nil
  | cons first _ ih =>
      exact .cons (node _ _ _ _ _ plan.1 first) (ih (plan.2 _ _ first))

/-- Contradiction and live source child graphs retain their actual recursive node entries. -/
theorem children {width : Nat}
    {call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → SourceEqualityPartialWorker.Result width}
    {check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Prop}
    (node : ∀ inherited value before result after, check inherited value before →
      call inherited value before = .done (.ok result) after → ReduceNode inherited value before result after)
    {payload values before results after}
    (trace : SourceEqualityInheritedChildren.Graph call payload values before results after)
    (plan : SourceEqualityPartialChecks.Children call check payload values before) :
    ReduceChildren payload values before results after := by
  cases trace with
  | contradiction => exact .contradiction
  | live actual => exact .live (walk node actual plan)

end MicroCFTA.SourceEqualityPartialLiftChildren
