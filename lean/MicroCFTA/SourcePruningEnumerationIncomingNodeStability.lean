import MicroCFTA.SourcePruningEnumerationIncomingNode
import MicroCFTA.SourcePruningEnumerationEnabledEmptyStability

/-!
# Successful incoming observations at larger work bounds

A representative-fuel error row is not a successful raw observation.
An empty raw result or one successful row excludes that error.
The same native completion and emptiness result retain every endpoint field.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A genuine successful raw observation retains its exact caller, query and read-state endpoints. -/
theorem run_ok_stable
    {checkEmpty : Bool} {r n p h R N P H : Nat}
    {caller reached : Caller width} {before read : Core EnumGuard}
    {uv : Nat} {incoming : Node} {incomingScs : List Suspended} {queries saved : Queries}
    {raw : List (Except EnumerationState.Error (Unit × Core EnumGuard))}
    (observed : run checkEmpty r n p h caller before uv incoming incomingScs queries =
      (.ok (some raw), reached, saved, read))
    (successful : raw = [] ∨ ∃ returned : Core EnumGuard, raw = [.ok ((), returned)])
    (enoughR : r ≤ R) (enoughN : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    run checkEmpty R N P H caller before uv incoming incomingScs queries =
      (.ok (some raw), reached, saved, read) := by
  have clean (fault : EnumerationState.Error) : raw ≠ [.error fault] := by
    intro same
    rcases successful with empty | ⟨returned, singleton⟩
    · rw [empty] at same
      cases same
    · rw [singleton] at same
      cases same
  cases representative : UnionFind.findRoot r before.representatives uv with
  | none =>
      have same := congrArg Prod.fst observed
      simp only [run, representative, Except.ok.injEq, Option.some.injEq] at same
      exact (clean .representativeFuel same.symm).elim
  | some found =>
      have representativeAt : UnionFind.findRoot R before.representatives uv = some found := by
        simpa only [Nat.add_sub_of_le enoughR] using
          UnionFind.findRoot_moreFuel r (R - r) before.representatives uv found representative
      cases stored : before.values[found.representative]? with
      | none =>
          simpa only [run, representative, representativeAt, stored] using observed
      | some value =>
          cases value with
          | eliminated | enumerated =>
              simpa only [run, representative, representativeAt, stored] using observed
          | unenumerated oldNode oldScs =>
              cases oldNode with
              | none =>
                  simpa only [run, representative, representativeAt, stored] using observed
              | some handle =>
                  cases decoded : lookupNode caller.checked.native.machine.heap handle with
                  | none =>
                      simpa only [run, representative, representativeAt, stored, decoded] using observed
                  | some old =>
                      cases native : SourceEqualityNativeDemand.execute n
                          (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                          caller.checked with
                      | yielded | failed | constraintError | blocked =>
                          have impossible := congrArg Prod.fst observed
                          simp only [run, representative, stored, decoded, native] at impossible
                          cases impossible
                      | done query queried =>
                          have nativeAt : SourceEqualityNativeDemand.execute N
                              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                              caller.checked = .done query queried := by
                            simpa only [Nat.add_sub_of_le enoughN] using
                              SourceEqualityNativeDemand.done_stable n (N - n) _ caller.checked queried query native
                          cases checkEmpty with
                          | false =>
                              simpa only [run, representative, representativeAt, stored, decoded, native, nativeAt,
                                Bool.false_eq_true, ↓reduceIte] using observed
                          | true =>
                              cases phase : SourcePruningEnumerationEnabledEmpty.check p h query queried caller.fourth queries with
                              | mk outcome returnedQueries =>
                                  cases outcome with
                                  | failed fault after fourth =>
                                      have impossible := congrArg Prod.fst observed
                                      simp only [run, representative, stored, decoded, native, ↓reduceIte, phase] at impossible
                                      cases impossible
                                  | done answer after fourth =>
                                      have phaseAt := SourcePruningEnumerationEnabledEmpty.check_done_stable
                                        p h P H query queried after caller.fourth fourth queries returnedQueries answer
                                        phase enoughP enoughH
                                      simpa only [run, representative, representativeAt, stored, decoded, native, nativeAt,
                                        ↓reduceIte, phase, phaseAt] using observed

/-- One actual successful incoming row retains its exact returned core and outer read state. -/
theorem run_singleton_stable
    {checkEmpty : Bool} {r n p h R N P H : Nat}
    {caller reached : Caller width} {before read returned : Core EnumGuard}
    {uv : Nat} {incoming : Node} {incomingScs : List Suspended} {queries saved : Queries}
    (observed : run checkEmpty r n p h caller before uv incoming incomingScs queries =
      (.ok (some [.ok ((), returned)]), reached, saved, read))
    (enoughR : r ≤ R) (enoughN : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    run checkEmpty R N P H caller before uv incoming incomingScs queries =
      (.ok (some [.ok ((), returned)]), reached, saved, read) :=
  run_ok_stable observed (.inr ⟨returned, rfl⟩) enoughR enoughN enoughP enoughH

end MicroCFTA.SourcePruningEnumerationIncomingNode
