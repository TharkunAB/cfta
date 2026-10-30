import MicroCFTA.SourcePruningEnumerationPathStorage
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

/-!
# Stored paths through actual incoming writes

The actual read retains all stored paths.
An incoming write appends its bucket to the actual stored bucket.
The explicit write law also covers raw rejection.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationPathStorage
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {P : EqualityTrie.Path → Prop}
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

private theorem finish_singleton_paths
    {before returned : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (valid : StatePaths P before) (inputs : BucketPaths P incomingScs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      [.ok ((), returned)]) : StatePaths P returned := by
  let written : Core :=
    {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other}
  have rawRun : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      match replacement with
      | .empty => []
      | _ => [.ok ((), written)] := by
    cases replacement <;> rfl
  rw [rawRun] at observed
  have coreSame : written = returned := by
    split at observed
    · cases observed
    · exact (Prod.mk.inj (Except.ok.inj (List.cons.inj observed).1)).2
  rw [← coreSame]
  have oldPaths : BucketPaths P oldScs :=
    valid (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored)
  have payload : BucketPaths P (references
      (.unenumerated (some handle) (incomingScs ++ oldScs) : UVarValue Symbol)) := by
    simpa only [references] using inputs.append oldPaths
  exact values_set_paths target (.unenumerated (some handle) (incomingScs ++ oldScs))
    valid payload rfl

private theorem finish_reply_paths
    {Fault : Type _} {before returned : Core} {target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (valid : StatePaths P before) (inputs : BucketPaths P incomingScs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : (Except.ok (some (ExceptT.run
        (finish target handle incomingScs oldScs replacement before))) : Except Fault (Option Raw)) =
      .ok (some [.ok ((), returned)])) : StatePaths P returned :=
  finish_singleton_paths valid inputs stored (Option.some.inj (Except.ok.inj observed))

variable {width : Nat}
section runtime
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual read and successful singleton retain the path predicate at every fixed bound. -/
theorem run_paths
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (valid : StatePaths P before) (inputs : BucketPaths P incomingScs) :
    StatePaths P (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2 ∧
      ∀ returned, (run checkEmpty r n p h caller before target incoming incomingScs queries).1 =
        .ok (some [.ok ((), returned)]) → StatePaths P returned := by
  generalize observedEq : run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold run at observedEq
  split at observedEq
  next =>
    simp only [Prod.mk.injEq] at observedEq
    rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨valid, ?_⟩
    intro returned singleton
    simp at singleton
  next =>
    repeat' first
      | (have readSame := congrArg (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) observedEq
         have resultSame := congrArg Prod.fst observedEq
         dsimp only at readSame resultSame
         constructor
         · rw [← readSame]
           change StatePaths P before
           exact valid
         · intro returned singleton
           rw [← resultSame] at singleton
           solve
           | simp at singleton
           | apply finish_reply_paths (P := P) (observed := singleton)
             · change StatePaths P before
               exact valid
             · exact inputs
             · assumption)
      | split at observedEq
      | (dsimp only at observedEq; split at observedEq)

end runtime

/-- The actual read and write preserve paths even when the raw continuation rejects. -/
theorem written_paths
    (before read after : Core) (fuel uv target handle : Nat) (oldNode : Option Nat)
    (incomingScs oldScs : List Suspended)
    (valid : StatePaths P before) (inputs : BucketPaths P incomingScs)
    (reading : Success (getValue fuel uv) before (.unenumerated oldNode oldScs) read)
    (shape : after = {read with
      values := read.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (read.expansionAncestry ++ read.recursionAncestry target).eraseDups
        else read.recursionAncestry other}) : StatePaths P after := by
  have readAndOld : StatePaths P read ∧ BucketPaths P oldScs := by
    obtain ⟨_found, _, stored, rfl⟩ := (getValue_success fuel uv before read
      (.unenumerated oldNode oldScs)).mp reading
    exact ⟨valid, valid (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored)⟩
  rw [shape]
  have payload : BucketPaths P (references
      (.unenumerated (some handle) (incomingScs ++ oldScs) : UVarValue Symbol)) := by
    simpa only [references] using inputs.append readAndOld.2
  exact values_set_paths target (.unenumerated (some handle) (incomingScs ++ oldScs))
    readAndOld.1 payload rfl

end MicroCFTA.SourcePruningEnumerationIncomingNode
