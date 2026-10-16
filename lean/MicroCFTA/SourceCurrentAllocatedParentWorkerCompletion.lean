import MicroCFTA.SourceCurrentAllocatedParentWorker
import MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedPartialGraph

/-!
# Stable literal execution of current parent-edge graphs

The supplied live graph retains its initial field lookup and exact local
and constructor returns. Rejected graphs skip both operations. Each graph
derives nine sufficient bounds without a physical or language premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion
open Language InternedConstructorTemplates
open SourceCurrentAllocatedParentWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard

/-- Nine sufficient stage bounds retain the same full parent return at all larger bounds. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Outcome A width)
    (result : A) (after : Checked width) (fourth : Fourth) (memo : Memo) : Prop :=
  ∃ g s r e p h m c n, ∀ G S R E P H M C N,
    g ≤ G → s ≤ S → r ≤ R → e ≤ E → p ≤ P → h ≤ H → m ≤ M → c ≤ C → n ≤ N →
      evaluation G S R E P H M C N = .done result after fourth memo

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A parent graph and its reached initial field receipt derive stable literal execution. -/
theorem edge_complete {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated}
    {inherited : EqValue} {values : List (Value Symbol Guard)} {before after : Checked width}
    {result : EdgeValue Symbol Guard} {fourth savedFourth : Fourth} {memo saved : Memo}
    (actual : SourceCurrentAllocatedParentEdge.Edge budget symbol original loaded inherited values before fourth memo
      result after savedFourth saved)
    (field : SourceEqualityMkEdgeAllocation.contradictory original = false →
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded)) :
    StableRun (fun g s r e p h m c n => edge g s r e p h m c n budget symbol original inherited values before fourth memo)
      result after savedFourth saved := by
  cases actual with
  | rejected test =>
      refine ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, ?_⟩
      intro G S R E P H M C N _ _ _ _ _ _ _ _ _
      simp only [edge, test, ite_true]
  | live test reduction built =>
      obtain ⟨g, s, r, e, p, h, m, c, n, stable⟩ :=
        SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete reduction
      refine ⟨g, s, r, e, p, h, m, c, n, ?_⟩
      intro G S R E P H M C N enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
      have completed := stable G S R E P H M C N enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
      simp only [edge, test, Bool.false_eq_true, ite_false, field test, reduceChildren, completed, Outcome.bind, build, built]

/-- The actual outer edge body already supplies the live field receipt at its own initial cache. -/
theorem edgeBody_complete {budget : Nat} {request : SourceCurrentAllocatedPartialState.EdgeRequest}
    {before after : Caller width} {result : EdgeValue Symbol Guard}
    (actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result after) :
    StableRun (fun g s r e p h m c n => edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge)
      result after.checked after.fourth after.merge := by
  cases actual with
  | parent field parent => exact edge_complete parent field

end MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion
