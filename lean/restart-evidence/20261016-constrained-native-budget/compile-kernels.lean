import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile

namespace NativeBudgetCompileChecks
open MicroCFTA Cache InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionThunks SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode
open SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain

/-- This full guard retains a nonempty equality class and an independent Boolean guard. -/
def fullGuard : Guard := ⟨some [[[0], [1]]], .and [.same [0] [1], .not .bottom]⟩

def nullary (symbol : Symbol) : Edge := .mk ⟨7, ⟨symbol, [], fullGuard⟩⟩ []

def unary (symbol : Symbol) : Edge := .mk ⟨8, ⟨symbol, [.empty], fullGuard⟩⟩ [.empty]

def leaf (symbol : Symbol) (identity : Nat) : Node := .node ⟨identity, .node [8]⟩ [unary symbol] 0 []

/-- The recurrence includes every occurrence of the complete expansion. -/
theorem numerical_expansion : nodeBudget 2 3 2 = 209 ∧ edgeBudget 2 3 2 = 628 := by decide

/-- Duplicate matching rows still reserve four edge calls and one node constructor. -/
theorem repeated_row_expansion [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) :
    Bound (scheme 2 0) (compileRows emptyDomain [nullary symbol, nullary symbol]
      [nullary symbol, nullary symbol]) 5 := by
  have profile : SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape 2 0 [nullary symbol, nullary symbol] := by
    simp [nullary, SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape,
      SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape,
      SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape]
  simpa only [nullary, MergedOrdinaryHeight.edgesHeight, MergedOrdinaryHeight.edgeHeight,
    MergedOrdinaryHeight.childrenHeight, Nat.max_self, nodeBudget] using
    rows_bound 2 0 [nullary symbol, nullary symbol] [nullary symbol, nullary symbol] profile profile (by simp) (by simp)

/-- Nonempty equality classes and arbitrary guards add no restriction to the structural query budget. -/
theorem guarded_node_expansion [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) :
    Bound (scheme 1 1) (compileNode ⟨emptyDomain, leaf symbol 20, leaf symbol 21⟩) 3 := by
  have profile : ∀ identity, SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape 1 1 (leaf symbol identity) := by
    intro identity
    simp [leaf, unary, SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape,
      SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape,
      SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape,
      SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape]
  simpa only [nodeCost, leaf, unary, MergedOrdinaryHeight.height, MergedOrdinaryHeight.edgesHeight,
    MergedOrdinaryHeight.edgeHeight, MergedOrdinaryHeight.childrenHeight, Nat.max_self, nodeBudget] using
    node_bound 1 1 ⟨emptyDomain, leaf symbol 20, leaf symbol 21⟩ ⟨rfl, profile 20, profile 21⟩

/-- The accepted nullary branch reserves one constructor for any actual combined constraint. -/
theorem nullary_children [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) :
    Bound (scheme 0 0)
      (SourceEqualityNativeCheckedCode.children emptyDomain (nullary symbol) (nullary symbol) combined) 1 := by
  have profile : SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape 0 0 (nullary symbol) := by
    simp [nullary, SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape,
      SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape]
  simpa only [edgeCost, edgeBudget, Nat.zero_mul, Nat.add_zero] using
    children_bound 0 0 ⟨emptyDomain, nullary symbol, nullary symbol⟩ ⟨rfl, profile, profile⟩ combined

/-- Sentinel construction requires no child profile and still reserves exactly one Work request. -/
theorem arbitrary_sentinel [DecidableEq (EdgeKey Symbol Guard)] (request : EdgeRequest Symbol Guard) :
    Bound (scheme 0 0) (SourceEqualityNativeCheckedCode.sentinel request.left) 1 := by
  simpa only [edgeCost, edgeBudget, Nat.zero_mul, Nat.add_zero] using sentinel_bound 0 0 request

/-- The literal mismatch yield retains its driver finish without a field lookup or completion premise. -/
theorem mismatch_driver [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} (rows arity : Nat) (request : EdgeRequest Symbol Guard)
    (inputs : EdgeInputs rows arity request) (before : SourceEqualityNativeDemand.State width) (handle : Nat)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    ControlBound (scheme rows arity)
      (.code ((SourceEqualityNativeCheckedCode.sentinel request.left).bind
        (fun result => .finishEdge handle result (.pure result)))) (edgeCost rows arity request) := by
  have yielded := SourceEqualityNativeDemand.body_mismatch request
    (fun result => .finishEdge handle result (.pure result)) before mismatch
  have checked := body_bound rows arity request inputs
    (fun result => .finishEdge handle result (.pure result)) before
    {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations}
    (.code ((SourceEqualityNativeCheckedCode.sentinel request.left).bind
      (fun result => .finishEdge handle result (.pure result)))) 0
    (fun _ => True.intro) yielded
  simpa only [Nat.add_zero] using checked

#print axioms numerical_expansion
#check @numerical_expansion
#print axioms repeated_row_expansion
#check @repeated_row_expansion
#print axioms guarded_node_expansion
#check @guarded_node_expansion
#print axioms nullary_children
#check @nullary_children
#print axioms arbitrary_sentinel
#check @arbitrary_sentinel
#print axioms mismatch_driver
#check @mismatch_driver
end NativeBudgetCompileChecks
