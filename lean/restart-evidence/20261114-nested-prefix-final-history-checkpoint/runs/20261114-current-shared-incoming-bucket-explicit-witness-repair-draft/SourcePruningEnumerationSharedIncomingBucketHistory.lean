import MicroCFTA.SourcePruningEnumerationSharedIncomingNode

/-!
# Full raw buckets at actual shared incoming writes

An actual shared incoming singleton supplies its canonical stored target.
Its write keeps the complete old bucket as an ordered suffix.
It copies the active ancestry and the target's old ancestry.
This receipt does not recover obligations after a later recursive clear.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedIncomingNode
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos

set_option autoImplicit false

private theorem finish_singleton_written
    {before returned : Core} {target handle : Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (observed : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      target handle incomingScs oldScs replacement before) = [.ok ((), returned)]) :
    returned = {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other} := by
  let written : Core := {before with
    values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
    recursionAncestry := fun other => if other = target then
      (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
      else before.recursionAncestry other}
  have rawRun : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
      target handle incomingScs oldScs replacement before) =
      match replacement with
      | .empty => []
      | _ => [.ok ((), written)] := by
    cases replacement <;> rfl
  rw [rawRun] at observed
  split at observed
  · cases observed
  · exact (Prod.mk.inj (Except.ok.inj (List.cons.inj observed).1)).2.symm

/-- Actual shared incoming success preserves each old raw obligation and its ancestry sources. -/
theorem singleton_bucket_history
    {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (after : Core) (afterCaller : Caller width) (savedQueries : Queries) (read : Core)
    (actual : run checkEmpty r n p h caller before target incoming incomingScs queries =
      (.ok (some [.ok ((), after)]), afterCaller, savedQueries, read)) :
    ∃ (found : UnionFind.Result) (oldNode : Option Nat) (oldScs : List Suspended) (handle : Nat),
      UnionFind.findRoot r before.representatives target = some found ∧
      before.values[found.representative]? = some (.unenumerated oldNode oldScs) ∧
      read = {before with representatives := found.forest} ∧
      after = {read with
        values := read.values.set found.representative
          (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = found.representative then
          (read.expansionAncestry ++ read.recursionAncestry found.representative).eraseDups
          else read.recursionAncestry other} ∧
      after.values[found.representative]? =
        some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      ∀ key, key ∈ after.recursionAncestry found.representative ↔
        key ∈ before.expansionAncestry ∨ key ∈ before.recursionAncestry found.representative := by
  suffices raw :
      ∃ (found : UnionFind.Result) (oldNode : Option Nat) (oldScs : List Suspended)
          (handle : Nat) (replacement : Node),
        UnionFind.findRoot r before.representatives target = some found ∧
        before.values[found.representative]? = some (.unenumerated oldNode oldScs) ∧
        read = {before with representatives := found.forest} ∧
        ExceptT.run (SourcePruningEnumerationIncomingNode.finish
          found.representative handle incomingScs oldScs replacement read) =
            [.ok ((), after)] by
    obtain ⟨found, oldNode, oldScs, handle, _replacement, lookup, slot, readSame, finished⟩ := raw
    have written := finish_singleton_written finished
    refine ⟨found, oldNode, oldScs, handle, lookup, slot, readSame, written, ?_, ?_⟩
    · have inside : found.representative < read.values.length := by
        rw [readSame]
        exact (List.getElem?_eq_some_iff.mp slot).1
      rw [written]
      exact List.getElem?_set_self inside
    · intro key
      simp only [written, readSame, ↓reduceIte, List.mem_eraseDups, List.mem_append]
  cases lookup : UnionFind.findRoot r before.representatives target with
  | none =>
      simp only [run, lookup] at actual
      cases actual
  | some found =>
      cases slot : before.values[found.representative]? with
      | none =>
          simp only [run, lookup, slot] at actual
          cases actual
      | some value =>
          cases value with
          | eliminated =>
              simp only [run, lookup, slot] at actual
              cases actual
          | enumerated fragment =>
              simp only [run, lookup, slot] at actual
              cases actual
          | unenumerated oldNode oldScs =>
              cases oldNode with
              | none =>
                  cases encoded : SourcePruningEnumerationNodes.encodeNode incoming with
                  | none =>
                      simp only [run, lookup, slot, encoded] at actual
                      cases actual
                  | some handle =>
                      have entered := actual
                      simp only [run, lookup, slot, encoded] at entered
                      have readSame : ({before with representatives := found.forest} : Core) = read :=
                        congrArg (fun result => result.2.2.2) entered
                      have finished : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
                          found.representative handle incomingScs oldScs incoming
                          ({before with representatives := found.forest} : Core)) = [.ok ((), after)] :=
                        Option.some.inj (Except.ok.inj (congrArg Prod.fst entered))
                      refine ⟨found, none, oldScs, handle, incoming, rfl, slot, readSame.symm, ?_⟩
                      rw [← readSame]
                      exact finished
              | some oldHandle =>
                  cases decoded : SourcePruningEnumerationNodes.lookupNode
                      caller.checked.native.machine.heap oldHandle with
                  | none =>
                      simp only [run, lookup, slot, decoded] at actual
                      cases actual
                  | some old =>
                      cases native : SourceEqualityNativeDemand.execute n
                          (.code (SourceRecursiveIntersectionCode.requestNode
                            IntersectionEmptyDomain.emptyDomain incoming old)) caller.checked with
                      | done query queried =>
                          rcases phaseObserved : (if checkEmpty then
                              SourcePruningEnumerationSharedEnabledEmpty.check p h query queried caller.fourth queries
                            else (.skipped queried caller.fourth, queries)) with
                            ⟨phase, phaseQueries⟩
                          have entered := actual
                          simp only [run, lookup, slot, decoded, native, phaseObserved] at entered
                          cases completed : phase.completed with
                          | none =>
                              simp only [completed] at entered
                              cases entered
                          | some answer =>
                              simp only [completed] at entered
                              cases encoded : SourcePruningEnumerationNodes.encodeNode
                                  (if answer then .empty else query) with
                              | none =>
                                  simp only [encoded] at entered
                                  cases entered
                              | some handle =>
                                  simp only [encoded] at entered
                                  have readSame :
                                      ({before with representatives := found.forest} : Core) = read :=
                                    congrArg (fun result => result.2.2.2) entered
                                  have finished : ExceptT.run (SourcePruningEnumerationIncomingNode.finish
                                      found.representative handle incomingScs oldScs
                                      (if answer then .empty else query)
                                      ({before with representatives := found.forest} : Core)) =
                                        [.ok ((), after)] :=
                                    Option.some.inj (Except.ok.inj (congrArg Prod.fst entered))
                                  refine ⟨found, some oldHandle, oldScs, handle,
                                    (if answer then .empty else query), rfl, slot, readSame.symm, ?_⟩
                                  rw [← readSame]
                                  exact finished
                      | yielded control current =>
                          simp only [run, lookup, slot, decoded, native] at actual
                          cases actual
                      | failed fault current =>
                          simp only [run, lookup, slot, decoded, native] at actual
                          cases actual
                      | constraintError message current =>
                          simp only [run, lookup, slot, decoded, native] at actual
                          cases actual
                      | blocked reason control current =>
                          simp only [run, lookup, slot, decoded, native] at actual
                          cases actual

end MicroCFTA.SourcePruningEnumerationSharedIncomingNode
