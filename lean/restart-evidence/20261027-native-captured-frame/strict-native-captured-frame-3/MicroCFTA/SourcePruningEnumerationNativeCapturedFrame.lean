import MicroCFTA.SourcePruningEnumerationDispatch
import MicroCFTA.SourcePruningEnumerationIncomingNode
import MicroCFTA.SourcePruningEnumerationNeutralLanguage

/-!
# Native observations with an unrelated captured payload removed

The bounds, native calls and query memos remain fixed.
The raw result retains every error and rejection branch.
Only enumeration states are mapped through payload neutralization.
These statements do not transport cached indexes.
-/
namespace MicroCFTA.SourcePruningEnumerationAssimilation
open EnumerationState EnumerationCorrectness EnumerationFrame
open SourcePruningEnumerationNeutralLanguage
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
variable {EnumGuard : Type}

/-- The same actual finish action commutes with removal of an unrelated payload. -/
theorem finish_neutral
    (held source target handle : Nat) (sourceScs targetScs : List Suspended)
    (replacement : Node) (before : EnumerationState.State Symbol EnumGuard)
    (sourceOther : source ≠ held) (targetOther : target ≠ held) :
    ExceptT.run (finish source target handle sourceScs targetScs replacement (neutralize held before)) =
      (ExceptT.run (finish source target handle sourceScs targetScs replacement before)).map
        (Except.map (fun row => (row.1, neutralize held row.2))) := by
  have commute := neutralize_assimilated held source target before
    (.unenumerated (some handle) (sourceScs ++ targetScs)) sourceOther targetOther
  cases replacement <;> first
    | rfl
    | exact congrArg (fun state : EnumerationState.State Symbol EnumGuard => [Except.ok ((), state)]) commute.symm

end MicroCFTA.SourcePruningEnumerationAssimilation

namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness EnumerationFrame
open SourcePruningEnumerationNeutralLanguage
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- Optional Empty rejection and every returned state retain the same raw branch shape. -/
theorem finishOptional_neutral
    (held source target : Nat) (node : Option Nat) (sourceScs targetScs : List Suspended)
    (before : EnumerationState.State Symbol EnumGuard)
    (sourceOther : source ≠ held) (targetOther : target ≠ held) :
    ExceptT.run (finishOptional source target node sourceScs targetScs (neutralize held before)) =
      (ExceptT.run (finishOptional source target node sourceScs targetScs before)).map
        (Except.map (fun row => (row.1, neutralize held row.2))) := by
  change (if node = some 0 then [] else
      [Except.ok ((), assimilated (neutralize held before) target source
        (.unenumerated node (sourceScs ++ targetScs)))]) =
    (if node = some 0 then [] else
      [Except.ok ((), assimilated before target source
        (.unenumerated node (sourceScs ++ targetScs)))]).map
      (Except.map (fun row => (row.1, neutralize held row.2)))
  split
  · rfl
  · exact congrArg (fun state : EnumerationState.State Symbol EnumGuard => [Except.ok ((), state)])
      (neutralize_assimilated held source target before
        (.unenumerated node (sourceScs ++ targetScs)) sourceOther targetOther).symm

/-- The complete dispatcher observation is equal when neither inspected slot is removed. -/
theorem dispatch_neutral
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (held : Nat) (checkEmpty : Bool) (nativeFuel p h : Nat)
    (caller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries)
    (sourceOther : source ≠ held) (targetOther : target ≠ held) :
    dispatch checkEmpty nativeFuel p h caller (neutralize held before) source target queries =
      dispatch checkEmpty nativeFuel p h caller before source target queries := by
  simp only [dispatch, neutralize_read held source before sourceOther,
    neutralize_read held target before targetOther]

end MicroCFTA.SourcePruningEnumerationDispatch

namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState EnumerationCorrectness EnumerationFrame
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- The incoming write and its hidden Empty rejection commute with an unrelated payload. -/
theorem finish_neutral
    (held target handle : Nat) (incomingScs oldScs : List Suspended)
    (replacement : Node) (before : EnumerationState.State Symbol EnumGuard) (different : target ≠ held) :
    ExceptT.run (finish target handle incomingScs oldScs replacement (neutralize held before)) =
      (ExceptT.run (finish target handle incomingScs oldScs replacement before)).map
        (Except.map (fun row => (row.1, neutralize held row.2))) := by
  have commute :
      neutralize held
        {before with
          values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
          recursionAncestry := fun other => if other = target then
            (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
            else before.recursionAncestry other} =
        {neutralize held before with
          values := (neutralize held before).values.set target
            (.unenumerated (some handle) (incomingScs ++ oldScs))
          recursionAncestry := fun other => if other = target then
            (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
            else before.recursionAncestry other} := by
    unfold neutralize
    congr 1
    exact List.set_comm (UVarValue.unenumerated (some handle) (incomingScs ++ oldScs) : UVarValue Symbol)
      (.unenumerated none []) different
  cases replacement <;> first
    | rfl
    | exact congrArg (fun state : EnumerationState.State Symbol EnumGuard => [Except.ok ((), state)]) commute.symm

/-- At fixed bounds, the same incoming execution retains its full caller and query memo. -/
theorem run_neutral
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (held : Nat) (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard) (uv : Nat) (incoming : Node)
    (incomingScs : List Suspended) (queries : Queries)
    (separate : ∀ found, UnionFind.findRoot r before.representatives uv = some found →
      found.representative ≠ held) :
    let observed := run checkEmpty r n p h caller before uv incoming incomingScs queries
    run checkEmpty r n p h caller (neutralize held before) uv incoming incomingScs queries =
      (observed.1.map (Option.map (List.map
        (Except.map (fun row => (row.1, neutralize held row.2))))),
        observed.2.1, observed.2.2.1, neutralize held observed.2.2.2) := by
  dsimp only
  have sameForest : (neutralize held before).representatives = before.representatives := rfl
  cases resolution : UnionFind.findRoot r before.representatives uv with
  | none => simp only [run, sameForest, resolution]; rfl
  | some found =>
      have different := separate found resolution
      have sameValue := neutralize_read held found.representative before different
      have readSame :
          {neutralize held before with representatives := found.forest} =
            neutralize held {before with representatives := found.forest} := rfl
      simp only [run, sameForest, resolution, sameValue, readSame]
      repeat' first
        | rfl
        | (rw [finish_neutral held found.representative _ incomingScs _ _
            {before with representatives := found.forest} different]; rfl)
        | split

/-- Initial class separation supplies the fixed-bound incoming locality condition. -/
theorem run_neutral_of_not_sameClass
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (held : Nat) (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard) (uv : Nat) (incoming : Node)
    (incomingScs : List Suspended) (queries : Queries)
    (separate : ¬ UnionFind.SameClass before.representatives held uv) :
    let observed := run checkEmpty r n p h caller before uv incoming incomingScs queries
    run checkEmpty r n p h caller (neutralize held before) uv incoming incomingScs queries =
      (observed.1.map (Option.map (List.map
        (Except.map (fun row => (row.1, neutralize held row.2))))),
        observed.2.1, observed.2.2.1, neutralize held observed.2.2.2) := by
  apply run_neutral held checkEmpty r n p h caller before uv incoming incomingScs queries
  intro found resolution same
  have path := (UnionFind.findRoot_correct r before.representatives uv found resolution).1
  have related : UnionFind.SameClass before.representatives uv held := by
    simpa only [same] using UnionFind.sameClass_root path
  exact separate (UnionFind.sameClass_symm related)

end MicroCFTA.SourcePruningEnumerationIncomingNode
