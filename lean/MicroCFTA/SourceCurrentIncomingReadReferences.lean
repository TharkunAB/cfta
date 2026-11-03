import MicroCFTA.SourceCurrentIncomingReadPending
import MicroCFTA.EnumerationReferences

/-! Original pending references remain valid at every literal incoming outer read. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingReadReferences
open EnumerationState EnumerationSchedule EnumerationReferences InternedConstructorTemplates
open EnumerationCanonicalUnion
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

private theorem pending_same_roots (before after : Core) (roots : Nat → Nat)
    (beforePaths : Roots before.representatives roots) (afterPaths : Roots after.representatives roots)
    (values : after.values = before.values) (pending : PendingReferences before) :
    PendingReferences after := by
  intro held fragment observed value member sc scMember sameClass
  have original : before.values[held]? = some (.enumerated fragment) := by
    rw [← values]
    exact observed
  have originalMember : value ∈ before.values := by
    rw [← values]
    exact member
  exact pending held fragment original value originalMember sc scMember
    ((class_iff _ roots beforePaths held sc.var).mpr
      ((class_iff _ roots afterPaths held sc.var).mp sameClass))

/-- Original root paths and pending references suffice for every actual outer read outcome. -/
theorem incoming_read_references (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (scs : List Suspended) (memos : Memos)
    (roots : Nat → Nat) (paths : Roots before.representatives roots)
    (pending : PendingReferences before) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    PendingReferences actual.2.2.2 := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  have actualFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before target incoming scs memos roots paths
  dsimp only at actualFacts
  exact pending_same_roots before _ roots paths actualFacts.1 actualFacts.2.1 pending

end MicroCFTA.SourceCurrentIncomingReadReferences
