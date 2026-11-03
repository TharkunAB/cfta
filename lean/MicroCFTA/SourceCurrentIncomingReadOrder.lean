import MicroCFTA.SourceCurrentIncomingReadRoots
import MicroCFTA.EnumerationOrder

/-! Actual incoming outer reads preserve the original dependency levels and frontier. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingReadOrder
open EnumerationState EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

/-- Original root paths and order derive order at the literal outer read on every outcome. -/
theorem incoming_read_order (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (scs : List Suspended) (memos : Memos)
    (roots : Nat → Nat) (paths : Roots before.representatives roots)
    (level : Nat → Nat) (frontier : Nat) (ordered : EnumerationOrder.Stratified before level frontier) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    EnumerationOrder.Stratified actual.2.2.2 level frontier := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  cases rootRead : UnionFind.findRoot r before.representatives target with
  | none =>
      simpa only [SourcePruningEnumerationIncomingNode.run, rootRead] using ordered
  | some found =>
      have total : UnionFind.Total before.representatives := by
        intro other
        obtain ⟨size, path⟩ := paths other
        exact ⟨roots other, size, path⟩
      have sourceObserved : SourceUnionFindCompression.findRoot r before.representatives target = some found := by
        rw [SourceUnionFindCompression.findRoot_eq]
        exact rootRead
      have readOrdered : EnumerationOrder.Stratified
          ({before with representatives := found.forest} : Core) level frontier :=
        ⟨(SourceUnionFindCompression.findRoot_satisfies total sourceObserved level).mpr ordered.classes,
          ordered.expanded, ordered.pending⟩
      simp only [SourcePruningEnumerationIncomingNode.run, rootRead]
      repeat' first | exact readOrdered | split

end MicroCFTA.SourceCurrentIncomingReadOrder
