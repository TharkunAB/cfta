import MicroCFTA.SourceCurrentIncomingReadRoots

/-! Original root admission fixes the first read target and all outer read root status. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingOriginalRoot
open EnumerationState EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

/-- The literal first incoming read retains an originally admitted root address. -/
theorem original_target (forest : UnionFind.Forest) (fuel target : Nat)
    (rooted : IsRoot forest target) (found : UnionFind.Result)
    (observed : UnionFind.findRoot fuel forest target = some found) :
    found.representative = target := by
  obtain ⟨size, selfPath⟩ := rooted
  have sourceObserved : SourceUnionFindCompression.findRoot fuel forest target = some found := by
    rw [SourceUnionFindCompression.findRoot_eq]
    exact observed
  have foundPath :=
    (SourceUnionFindCompression.findRoot_correct fuel forest target found sourceObserved).1
  exact (UnionFind.reaches_unique foundPath selfPath).1

private theorem root_status (before after : UnionFind.Forest) (roots : Nat → Nat)
    (beforePaths : Roots before roots) (afterPaths : Roots after roots) (target : Nat) :
    IsRoot after target ↔ IsRoot before target := by
  constructor
  · rintro ⟨size, selfPath⟩
    obtain ⟨oldSize, oldPath⟩ := beforePaths target
    obtain ⟨newSize, newPath⟩ := afterPaths target
    have same : roots target = target := (UnionFind.reaches_unique newPath selfPath).1
    exact ⟨oldSize, by simpa only [same] using oldPath⟩
  · rintro ⟨size, selfPath⟩
    obtain ⟨oldSize, oldPath⟩ := beforePaths target
    obtain ⟨newSize, newPath⟩ := afterPaths target
    have same : roots target = target := (UnionFind.reaches_unique oldPath selfPath).1
    exact ⟨newSize, by simpa only [same] using newPath⟩

/-- Every actual incoming outer read retains the original root status at each address. -/
theorem incoming_read_root_status (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (scs : List Suspended) (memos : Memos)
    (roots : Nat → Nat) (paths : Roots before.representatives roots) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    ∀ other, IsRoot actual.2.2.2.representatives other ↔ IsRoot before.representatives other := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before target incoming scs memos roots paths
  dsimp only at readFacts
  intro other
  exact root_status before.representatives _ roots paths readFacts.1 other

end MicroCFTA.SourceCurrentIncomingOriginalRoot
