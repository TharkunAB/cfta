import MicroCFTA.SourceCurrentIncomingReadRoots
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter
import MicroCFTA.EnumerationDependencies

/-! Original pending buckets remain admitted at every actual incoming outer read. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingReadPending
open EnumerationState EnumerationSchedule EnumerationDependencies InternedConstructorTemplates
open EnumerationCanonicalUnion
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

private theorem pending_same_roots (before after : Core) (roots : Nat → Nat)
    (remaining : List Suspended) (beforePaths : Roots before.representatives roots)
    (afterPaths : Roots after.representatives roots) (values : after.values = before.values)
    (pending : InputsPending before remaining) : InputsPending after remaining := by
  intro held fragment observed sc member sameClass
  have original : before.values[held]? = some (.enumerated fragment) := by
    rw [← values]
    exact observed
  exact pending held fragment original sc member
    ((class_iff _ roots beforePaths held sc.var).mpr
      ((class_iff _ roots afterPaths held sc.var).mp sameClass))

/-- Original pending facts and root paths derive admission at the literal returned read Core. -/
theorem incoming_read_pending (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (scs remaining : List Suspended) (memos : Memos)
    (roots : Nat → Nat) (paths : Roots before.representatives roots)
    (pending : InputsPending before remaining) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    InputsPending actual.2.2.2 remaining := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  have actualFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before target incoming scs memos roots paths
  dsimp only at actualFacts
  exact pending_same_roots before _ roots remaining paths actualFacts.1 actualFacts.2.1 pending

end MicroCFTA.SourceCurrentIncomingReadPending
