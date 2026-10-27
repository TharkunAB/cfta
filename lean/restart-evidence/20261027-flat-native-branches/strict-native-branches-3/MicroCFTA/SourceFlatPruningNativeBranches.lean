import MicroCFTA.SourceFlatPruningCapturedEdge
import MicroCFTA.SourcePruningEnumerationNativeBranches

/-!
# Ordered native alternatives with a fixed captured flat cache

Each sibling restores the captured enumeration cache.
Only the actual reached native caller and query table pass to the next sibling.
-/

namespace MicroCFTA.SourceFlatPruningNativeBranches
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Receipt" => SourceFlatPruningSelectedEdge.Result
variable {width : Nat}

/-- Keep every processed receipt and the exact first unsupported observation. -/
inductive Result (width : Nat) where
  /-- Every alternative supplies a continuable native endpoint. -/
  | complete (processed : List (Receipt width)) (caller : Caller width) (queries : Queries)
  /-- Retain the finished prefix and the current optional receipt. -/
  | stopped (processed : List (Receipt width)) (current : Option (Receipt width))

/-- Continue completed edges, arity rejections and valid child rejections. -/
def advance : Receipt width → Option (Caller width × Queries)
  | .complete _ caller queries _ => some (caller, queries)
  | .rejected caller queries _ => some (caller, queries)
  | .stopped _ (.ok (some []), caller, queries, _outer, _waiting) (some _) => some (caller, queries)
  | _ => none

/-- Relate ordered native receipts, which include caller data in Type 1. -/
inductive ReceiptsRelated : List (Receipt width) →
    List (SourcePruningEnumerationSelectedEdge.Result width) → Prop where
  /-- Empty receipt lists agree. -/
  | nil : ReceiptsRelated [] []
  /-- Related heads retain their position before related suffixes. -/
  | cons : SourceFlatPruningSelectedEdge.ResultRelated first second →
      ReceiptsRelated rest tail → ReceiptsRelated (first :: rest) (second :: tail)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Scan siblings with the captured cache and each actual returned native endpoint. -/
noncomputable def run (checkEmpty : Bool) (nativeFuel p h target : Nat) (scs : List Suspended)
    (before : Cached) : List (EdgeValue Symbol Constraint) → Caller width → Queries → Result width
  | [], caller, queries => .complete [] caller queries
  | edge :: rest, caller, queries =>
      match SourceFlatPruningCapturedEdge.run checkEmpty nativeFuel p h target scs edge caller before queries with
      | none => .stopped [] none
      | some receipt =>
          match advance receipt with
          | none => .stopped [] (some receipt)
          | some (middleCaller, middleQueries) =>
              match run checkEmpty nativeFuel p h target scs before rest middleCaller middleQueries with
              | .complete processed afterCaller saved => .complete (receipt :: processed) afterCaller saved
              | .stopped processed current => .stopped (receipt :: processed) current

/-- Relate ordered receipts, optional stopping observations and literal native effects. -/
def ResultRelated (flat : Result width) (earlier : SourcePruningEnumerationNativeBranches.Result width) : Prop :=
  match flat, earlier with
  | .complete processed caller queries, .complete oldProcessed oldCaller oldQueries =>
      ReceiptsRelated processed oldProcessed ∧
        caller = oldCaller ∧ queries = oldQueries
  | .stopped processed current, .stopped oldProcessed oldCurrent =>
      ReceiptsRelated processed oldProcessed ∧
        match current, oldCurrent with
        | none, none => True
        | some first, some second => SourceFlatPruningSelectedEdge.ResultRelated first second
        | _, _ => False
  | _, _ => False

end MicroCFTA.SourceFlatPruningNativeBranches
