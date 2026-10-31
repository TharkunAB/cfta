import MicroCFTA.SourceCurrentIncomingAdaptObserved
import MicroCFTA.SourceUnionFindCompression
import MicroCFTA.SourcePruningEnumerationIncomingNode

/-! Literal incoming reads retain entry roots and the adapter uses the reached heap. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingReadRoots
open EnumerationState EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

private theorem compressed_roots (forest : UnionFind.Forest) (roots : Nat → Nat)
    (fuel target : Nat) (found : UnionFind.Result) (paths : Roots forest roots)
    (observed : UnionFind.findRoot fuel forest target = some found) :
    Roots found.forest roots := by
  have sourceObserved : SourceUnionFindCompression.findRoot fuel forest target = some found := by
    rw [SourceUnionFindCompression.findRoot_eq]
    exact observed
  intro other
  obtain ⟨size, path⟩ := paths other
  exact ⟨size, (SourceUnionFindCompression.findRoot_correct fuel forest target found sourceObserved).2 path⟩

/-- Every literal incoming outcome retains the entry root function, values and counter. -/
theorem incoming_read_roots (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (scs : List Suspended) (memos : Memos)
    (roots : Nat → Nat) (paths : Roots before.representatives roots) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    Roots actual.2.2.2.representatives roots ∧
      actual.2.2.2.values = before.values ∧ actual.2.2.2.counter = before.counter := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  cases rootRead : UnionFind.findRoot r before.representatives target with
  | none =>
      simpa only [SourcePruningEnumerationIncomingNode.run, rootRead] using
        (show Roots before.representatives roots ∧ before.values = before.values ∧
          before.counter = before.counter from ⟨paths, rfl, rfl⟩)
  | some found =>
      have readFacts : Roots ({before with representatives := found.forest} : Core).representatives roots ∧
          ({before with representatives := found.forest} : Core).values = before.values ∧
          ({before with representatives := found.forest} : Core).counter = before.counter :=
        ⟨compressed_roots before.representatives roots r target found paths rootRead, rfl, rfl⟩
      simp only [SourcePruningEnumerationIncomingNode.run, rootRead]
      repeat' first | exact readFacts | split

/-- Actual incoming cache returns derive counts at the reached heap and original target. -/
theorem incoming_cache_observed (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (scs : List Suspended) (memos : Memos)
    (after : Cached) (roots : Nat → Nat) (paths : Roots before.core.representatives roots) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query).2 = some after →
      after.waiting = EnumerationCanonicalWaiting.count roots 1 scs before.waiting ∧
        ∀ otherFuel other, (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h otherFuel
          caller before target incoming scs memos.query).2 = some other → after = other := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  intro observed
  have readFacts := incoming_read_roots symbolEquality edgeEquality nodeEquality checkEmpty r n p h
    caller before.core target incoming scs memos roots paths
  dsimp only at readFacts
  generalize incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before.core target incoming scs memos.query = actual
  rcases actual with ⟨result, nextCaller, savedQueries, read⟩
  rw [incomingObserved] at readFacts
  cases result with
  | error fault => simp [SourcePruningEnumerationIncomingCacheAdapter.run, incomingObserved] at observed
  | ok output =>
      cases output with
      | none => simp [SourcePruningEnumerationIncomingCacheAdapter.run, incomingObserved] at observed
      | some raw =>
          have adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt nextCaller.checked.native.machine.heap
              k target scs before read raw = some after := by
            simpa only [SourcePruningEnumerationIncomingCacheAdapter.run, incomingObserved] using observed
          have actual := SourceCurrentIncomingAdaptObserved.adapt_observed nextCaller.checked.native.machine.heap
            before read raw k target scs after roots readFacts.1 adapted
          refine ⟨actual.1, ?_⟩
          intro otherFuel other otherObserved
          apply actual.2 otherFuel other
          simpa only [SourcePruningEnumerationIncomingCacheAdapter.run, incomingObserved] using otherObserved

end MicroCFTA.SourceCurrentIncomingReadRoots
