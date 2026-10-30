import MicroCFTA.SourcePruningEnumerationPathSelectedRaw
import MicroCFTA.SourcePruningEnumerationPathIncoming

/-!
# Paths in every successful raw incoming row

The actual writer preserves the original path predicate at every raw row.
Native fault results do not require a Context premise.
-/
namespace MicroCFTA.SourcePruningEnumerationPathIncomingRaw
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationPathTransport SourcePruningEnumerationPathStorage
open SourcePruningEnumerationPathSelectedRaw (RawPaths)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat} {P : EqualityTrie.Path → Prop}
local notation "Core" => EnumerationState.State Symbol EnumGuard

private theorem finish_raw_paths
    (before : Core) (target handle : Nat) (oldNode : Option Nat)
    (incomingScs oldScs : List Suspended) (replacement : Node)
    (paths : StatePaths P before) (inputs : BucketPaths P incomingScs)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs)) :
    RawPaths P (ExceptT.run
      (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement before)) := by
  let written : Core :=
    {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other}
  have rawRun : ExceptT.run
      (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement before) =
      match replacement with
      | .empty => []
      | _ => [.ok ((), written)] := by
    cases replacement <;> rfl
  intro result after member
  rw [rawRun] at member
  split at member
  · simp at member
  · have same := List.mem_singleton.mp member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
    have oldPaths : BucketPaths P oldScs :=
      paths (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored)
    have payload : BucketPaths P (references
        (.unenumerated (some handle) (incomingScs ++ oldScs) : UVarValue Symbol)) := by
      simpa only [references] using inputs.append oldPaths
    exact values_set_paths target (.unenumerated (some handle) (incomingScs ++ oldScs))
      paths payload rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every successful raw incoming row retains the original stored paths. -/
theorem run_raw_paths
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (paths : StatePaths P before) (inputs : BucketPaths P incomingScs) :
    match (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming incomingScs queries).1 with
    | .ok (some raw) => RawPaths P raw
    | _ => True := by
  generalize observedEq : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before target incoming incomingScs queries = observed
  obtain ⟨result, reached, saved, read⟩ := observed
  dsimp only
  unfold SourcePruningEnumerationIncomingNode.run at observedEq
  repeat' first
    | (have resultSame := congrArg Prod.fst observedEq
       dsimp only at resultSame
       rw [← resultSame]
       solve
       | (intro result after member; simp at member)
       | trivial
       | (apply finish_raw_paths
          · change StatePaths P before
            exact paths
          · exact inputs
          · assumption))
    | split at observedEq
    | (dsimp only at observedEq; split at observedEq)

end MicroCFTA.SourcePruningEnumerationPathIncomingRaw
