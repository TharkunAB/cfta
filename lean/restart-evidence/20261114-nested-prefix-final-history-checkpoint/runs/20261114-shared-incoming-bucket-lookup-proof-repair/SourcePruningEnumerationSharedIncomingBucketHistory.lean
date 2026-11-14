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
  unfold run at actual
  cases lookup : UnionFind.findRoot r before.representatives target with
  | none =>
      simp only [lookup] at actual
      cases actual
  | some found =>
      simp only [lookup] at actual
      repeat' split at actual
      all_goals
        have resultSame := congrArg Prod.fst actual
        dsimp only at resultSame
        try (solve | simp at resultSame)
      all_goals
        have readSame := congrArg (fun result : _ × Caller width × Queries × Core =>
          result.2.2.2) actual
        dsimp only at readSame
        have written := finish_singleton_written
          (Option.some.inj (Except.ok.inj resultSame))
        refine ⟨found, _, _, _, rfl, ?_, readSame.symm, ?_, ?_, ?_⟩
        · assumption
        · rw [← readSame]
          exact written
        · have stored : ∃ oldNode oldScs,
              before.values[found.representative]? = some (.unenumerated oldNode oldScs) := by
            exact ⟨_, _, by assumption⟩
          obtain ⟨oldNode, oldScs, slot⟩ := stored
          have inside : found.representative < before.values.length :=
            (List.getElem?_eq_some_iff.mp slot).1
          rw [written]
          exact List.getElem?_set_self inside
        · intro key
          simp only [written, ↓reduceIte, List.mem_eraseDups, List.mem_append]

end MicroCFTA.SourcePruningEnumerationSharedIncomingNode
