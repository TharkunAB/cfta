import MicroCFTA.SourceCurrentAllocatedSharedPartialGraph
import MicroCFTA.SourceCurrentSharedParentNumeric

/-!
# Endpoint-associated reads for the shared outer graph

The eight relations retain the same observed graph and ordered memo bundles.
Each parent leaf carries a canonical numeric receipt with the same original
caller, result, checked state, fourth memo, merge memo and global bundle.
The observed parent bounds and canonical receipt bounds can differ.
No read schedule is reindexed to the observed bounds. No equality between
an observed trace and a canonical trace is asserted.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedPartialEndpointReads
open InternedConstructorTemplates
open SourceCurrentAllocatedSharedPartialGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "NodeReq" => SourceCurrentAllocatedPartialState.NodeRequest
local notation "EdgeReq" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Merge" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

mutual
/-- A returned node hit skips body reads; evaluation uses exactly its selected body. -/
inductive NodeCallReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {request : NodeReq} → {before : Caller width} → {result : Value Symbol Guard} → {after : Caller width} →
    NodeCall budget request before result after → Memos → Memos → Prop where
  | hit : NodeCallReads formulas solver (.hit started) memos memos
  | evaluate (reads : NodeBodyReads formulas solver body memos saved) :
      NodeCallReads formulas solver (.evaluate started body) memos saved

/-- Ordinary bodies follow rows; the other source node branches make no global query. -/
inductive NodeBodyReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {request : NodeReq} → {before : Caller width} → {result : Value Symbol Guard} → {after : Caller width} →
    NodeBody budget request before result after → Memos → Memos → Prop where
  | empty : NodeBodyReads formulas solver .empty memos memos
  | union : NodeBodyReads formulas solver .union memos memos
  | binder : NodeBodyReads formulas solver (.binder actual) memos memos
  | ordinary (reads : RowsReads formulas solver rows memos saved) :
      NodeBodyReads formulas solver (.ordinary rows) memos saved

/-- Edge result hits skip the checked parent body; evaluation retains its literal reads. -/
inductive EdgeCallReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {request : EdgeReq} → {before : Caller width} → {result : EdgeValue Symbol Guard} → {after : Caller width} →
    EdgeCall budget request before result after → Memos → Memos → Prop where
  | hit : EdgeCallReads formulas solver (.hit started) memos memos
  | evaluate (reads : EdgeBodyReads formulas solver body memos saved) :
      EdgeCallReads formulas solver (.evaluate started body) memos saved

/-- A parent leaf associates its observed return with a canonical receipt at the same endpoint. -/
inductive EdgeBodyReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {request : EdgeReq} → {before : Caller width} → {result : EdgeValue Symbol Guard} → {after : Caller width} →
    EdgeBody budget request before result after → Memos → Memos → Prop where
  | parent {budget g s r e p h m c n : Nat} {inherited : EqValue}
      {edge result : EdgeValue Symbol Guard} {before : Caller width} {checked : Checked width}
      {fourth : Fourth} {merge : Merge} {memos saved : Memos}
      {actual : SourceCurrentAllocatedSharedParentWorker.edge g s r e p h m c n budget
        edge.entry.key.symbol edge.entry.key.constraint inherited edge.children
        before.checked before.fourth before.merge = .done result checked fourth merge}
      {inventory : Inventory} {profile : Profile} {loaded : Allocated}
      (receipt : SourceCurrentSharedParentNumeric.Receipt formulas solver inventory profile budget
        edge.entry.key.symbol edge.entry.key.constraint loaded inherited edge.children before memos
        result checked fourth merge saved) :
      EdgeBodyReads formulas solver (.parent g s r e p h m c n actual) memos saved

/-- Each source row reads its parent call, then descendants, and then the row suffix. -/
inductive RowsReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {inherited : EqValue} → {values : List (EdgeValue Symbol Guard)} → {before : Caller width} →
    {results : List (EdgeValue Symbol Guard)} → {after : Caller width} →
    Rows budget inherited values before results after → Memos → Memos → Prop where
  | nil : RowsReads formulas solver .nil memos memos
  | cons (edge : EdgeCallReads formulas solver first memos middle)
      (children : DescendantsReads formulas solver child middle later)
      (rest : RowsReads formulas solver tail later saved) :
      RowsReads formulas solver (.cons first child tail) memos saved

/-- The inherited prefix and raw rebuild surround the actual child-query reads. -/
inductive DescendantsReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {inherited : EqValue} → {value : EdgeValue Symbol Guard} → {before : Caller width} →
    {result : EdgeValue Symbol Guard} → {after : Caller width} →
    Descendants budget inherited value before result after → Memos → Memos → Prop where
  | run (reads : ChildrenReads formulas solver children memos saved) :
      DescendantsReads formulas solver (.run combined children) memos saved

/-- Contradiction has no child call; a live inherited value follows its indexed walk. -/
inductive ChildrenReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {inherited : EqValue} → {values : List (Value Symbol Guard)} → {before : Caller width} →
    {results : List (Value Symbol Guard)} → {after : Caller width} →
    Children budget inherited values before results after → Memos → Memos → Prop where
  | contradiction : ChildrenReads formulas solver .contradiction memos memos
  | live (reads : WalkReads formulas solver actual memos saved) :
      ChildrenReads formulas solver (.live actual) memos saved

/-- Actual descended requests thread global reads from the head through the remaining slots. -/
inductive WalkReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {combined : EqValue} → {index : Nat} → {values : List (Value Symbol Guard)} → {before : Caller width} →
    {results : List (Value Symbol Guard)} → {after : Caller width} →
    Walk budget combined index values before results after → Memos → Memos → Prop where
  | nil : WalkReads formulas solver .nil memos memos
  | cons (head : NodeCallReads formulas solver first memos middle)
      (rest : WalkReads formulas solver tail middle saved) :
      WalkReads formulas solver (.cons first tail) memos saved
end

/-- A node result hit cannot change the global bundle in this actual read schedule. -/
theorem node_hit {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {budget : Nat} {request : NodeReq}
    {before running : Caller width} {handle : Nat} {result : Value Symbol Guard} {memos saved : Memos}
    (started : SourceCurrentAllocatedPartialState.beginNode request before = (handle, (.ready result, running)))
    (reads : NodeCallReads formulas solver (NodeCall.hit (budget := budget) started) memos saved) : saved = memos := by
  cases reads <;> simp_all

/-- An edge result hit skips the body and leaves every global query table unchanged. -/
theorem edge_hit {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {budget : Nat} {request : EdgeReq}
    {before running : Caller width} {handle : Nat} {result : EdgeValue Symbol Guard} {memos saved : Memos}
    (started : SourceCurrentAllocatedPartialState.beginEdge request before = (handle, (.ready result, running)))
    (reads : EdgeCallReads formulas solver (EdgeCall.hit (budget := budget) started) memos saved) : saved = memos := by
  cases reads <;> simp_all

/-- The contradiction branch has no child call and retains the literal incoming global bundle. -/
theorem children_contradiction {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {budget : Nat} {values : List (Value Symbol Guard)}
    {before : Caller width} {memos saved : Memos}
    (reads : ChildrenReads formulas solver (Children.contradiction (budget := budget) (values := values) (before := before)) memos saved) :
    saved = memos := by
  cases reads
  rfl


/-- A parent endpoint association exposes its canonical receipt without changing observed bounds. -/
theorem parent_receipt {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {budget g s r e p h m c n : Nat}
    {inherited : EqValue} {edge result : EdgeValue Symbol Guard} {before : Caller width}
    {checked : Checked width} {fourth : Fourth} {merge : Merge} {memos saved : Memos}
    {actual : SourceCurrentAllocatedSharedParentWorker.edge g s r e p h m c n budget
      edge.entry.key.symbol edge.entry.key.constraint inherited edge.children
      before.checked before.fourth before.merge = .done result checked fourth merge}
    (reads : EdgeBodyReads formulas solver (.parent g s r e p h m c n actual) memos saved) :
    ∃ inventory profile loaded, SourceCurrentSharedParentNumeric.Receipt formulas solver inventory profile budget
      edge.entry.key.symbol edge.entry.key.constraint loaded inherited edge.children before memos
      result checked fourth merge saved := by
  cases reads with
  | parent receipt => exact ⟨_, _, _, receipt⟩

end MicroCFTA.SourceCurrentAllocatedSharedPartialEndpointReads
